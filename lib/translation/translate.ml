open ArduinoSyntax.Syntax
open Why3
open Utils

let bindings : (string,Ptree.ident) Hashtbl.t = Hashtbl.create 100





(* only over integers for now *)
let translate_binop op = 
  let symb = match op with 
  | Add -> "+" | Sub -> "-" | Mul -> "*"  | Div -> "/"
  | Gt -> ">"  | Lt -> "<"  | Gte -> ">=" | Lte -> "<="
  | Eq -> "="
  in Ptree_helpers.qualid ["Int"; Ident.op_infix symb]


let rec translate_expression (e:expr) : Ptree.expr = 
  match e with
  | True -> expr Etrue
  | False -> expr Efalse
  | Int n -> econst n
  | Var s -> evar (Qident (ident s))
  | Read s ->       
    let qid = Ptree_helpers.qualid ["Ref";Ident.op_prefix "!"] in
    eapply (evar qid) (evar (Qident (ident s)))

  | BinOp (e1,binop,e2) -> eapp (translate_binop binop) [translate_expression e1; translate_expression e2]


let rec translate_fol (f:fol) : Ptree.term = 
  match f with
  | FOL_True -> term Ttrue
  | FOL_False -> term Tfalse
  (* | Pred p -> term (T) *)
  | FOL_Not t -> Tnot (translate_fol t) |> term
  (* | And (t1,t2) ->  Tinfix (translate_formula t1) "" (translate_formula t2) |> term *)
  (* | Or (t1,t2) -> t_or (translate_formula t1) (translate_formula t2) *)
  (* | Imp (t1,t2) -> t_implies (translate_formula t1) (translate_formula t2) *)
  (* | Forall (v,f) -> t_forall (t_close_quant v) (translate_formula f)
  | Exists (v,f) -> t_exists v (translate_formula f) *)
  | _ -> failwith "not supported yet"

let translate_pltl f = ignore f; failwith "todo"

let translate_formula = function FOL f -> translate_fol f | PLTL f -> translate_pltl f


let rec translate_statements (s: stmt list) : Ptree.expr = 
  let open Ptree in 
  let aux = function
  | Assign (id, e) -> Eassign [( (evar (Qident (ident id)), None, translate_expression e))] |> expr
  | Emit (id,e) -> Eassign [(translate_expression e, None, (evar (Qident (ident id))))] |> expr (* will need to be treated differently *)
  | If (e,t,f) -> 
    let f = Option.fold ~some:translate_statements f ~none:(Etuple [] |> expr) in 
    Eif (translate_expression e, translate_statements t, f) |> expr 

  | While (e,inv,_v,stmt) -> Ewhile (translate_expression e, [translate_fol inv], [], translate_statements stmt) |> expr
  in
  List.fold_left (fun x y -> Esequence (expr x,(aux y))) (Etuple []) s |> expr


(* for now, single while(true) loop *)
let make_loop (body:Ptree.expr) inv = 
  let open Ptree in
  Ewhile (expr Etrue,inv,[], body) |> expr



let generate_declarations = ()


let translate_program (p : program) : Ptree.mlw_file = 
  let open Ptree in
  (* let lib =  *)
  (* print_string Env.base_language; *)

  let use_int_Int = use ~import:false (["int";"Int"]) in
  let use_ref_Ref = use ~import:false (["ref";"Ref"]) in
  let use_option_Option = use ~import:false (["option";"Option"]) in
  let use_list_List = use ~import:false (["list";"List"]) in
  let use_list_Length = use ~import:false (["list";"Length"]) in


  let sp_pre = [translate_formula p.prog_requires] in
  let inv = translate_formula p.prog_ensures in
  let sp_post = [Loc.dummy_position, [pat Pwild, inv]] in
  let spec = { Ptree_helpers.empty_spec with sp_pre ; sp_post ; sp_diverge = true} in
  let body : Ptree.expr = translate_statements p.prog_main.main_body in
  let loop = make_loop body [inv] in

  let main : decl = 
    Efun ([], None, pat Pwild, Ity.MaskVisible, spec, loop) 
    |> expr 
    |> fun m ->  Dlet (ident "main", false, Expr.RKnone, m)
  in

  let m = (ident "Program", 
    [use_int_Int; use_ref_Ref; use_option_Option; use_list_List; use_list_Length
    ; main
    ]) 
  in Ptree.Modules [m]