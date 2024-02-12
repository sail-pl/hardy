open ArduinoSyntax.Syntax
open Why3

module H = Ptree_helpers
module P = Ptree

let unit_val = Why3.Ptree.Etuple []


let bindings : (string,Ptree.ident) Hashtbl.t = Hashtbl.create 100


(* only over integers for now *)
let translate_binop op = 
  let symb = match op with 
  | Add -> "+" | Sub -> "-" | Mul -> "*"  | Div -> "/"
  | Gt -> ">"  | Lt -> "<"  | Gte -> ">=" | Lte -> "<="
  | Eq -> "="
  in Ptree_helpers.qualid [Ident.op_infix symb]


let rec translate_expression ({value=e;loc}:expr) : Ptree.expr = 
  let loc = Loc.extract loc in 
  match e with
  | True -> H.expr ~loc Etrue
  | False -> H. expr ~loc  Efalse
  | Int n -> H.econst n ~loc
  | Var s -> 
    let deref = H.qualid [Ident.op_prefix "!"] in 
    H.eapp ~loc deref H.[[s] |> qualid |> evar]
    
  | Read s -> Ptree.Easref (H.qualid [s]) |> H.expr ~loc

  | BinOp (e1,binop,e2) -> H.eapp ~loc (translate_binop binop) [translate_expression e1; translate_expression e2]


let rec translate_term ({value=t;loc}:expr) : Ptree.term =
  let loc = Loc.extract loc in 
  match t with
  | True -> H.term ~loc Ttrue
  | False -> H.term ~loc Tfalse
  | Int n -> H.tconst ~loc n
  | Var s -> [s] |> H.qualid |> H.tvar ~loc
  | Read s ->       
    Ptree.Tasref (H.qualid [s]) |> H.term ~loc

  | BinOp (e1,binop,e2) -> H.tapp ~loc (translate_binop binop) [translate_term e1; translate_term e2]



let rec translate_fol ({value=f;loc}:fol) : Ptree.term = 
  let loc = Loc.extract loc in 
  let open H in 
  let open P in 
  match f with
  | FOL_True -> term ~loc Ttrue
  | FOL_False -> term ~loc Tfalse
  | Pred p -> translate_term p 
  | FOL_Not t -> Tnot (translate_fol t) |> term ~loc
  | And (t1,t2) -> Tbinop  ((translate_fol t1), Dterm.DTand, (translate_fol t2)) |> term ~loc
  | FOL_Or (t1,t2) -> Tbinop  ((translate_fol t1), Dterm.DTor, (translate_fol t2)) |> term ~loc
  | Arrow (t1,t2) -> Tbinop ((translate_fol t1), Dterm.DTimplies, (translate_fol t2)) |> term ~loc
  | Forall (v,f) -> Tquant (DTforall,  one_binder v, [], (translate_fol f)) |> term ~loc
  | Exists (v,f) ->  Tquant (DTexists,  one_binder v, [], (translate_fol f)) |> term ~loc

let translate_pltl f = ignore f; failwith "todo"

let translate_formula = function FOL f -> translate_fol f | PLTL f -> translate_pltl f


let rec translate_statements (s: stmt list) : Ptree.expr = 
  let open P in 
  let open H in 
  let aux {value=s;loc} = 
    let loc = Loc.extract loc in match s with
    | Assign (id, e) ->
      let assgn = qualid [Ident.op_infix ":="] in 
      eapp ~loc assgn [([id] |> qualid |> evar) ; translate_expression e]

    | Emit (id,e) -> Eassign [(translate_expression e, None, ([id] |> qualid |> evar))] |> expr ~loc (* will need to be treated differently *)
    | If (e,t,f) -> 
      let f = Option.fold ~some:translate_statements f ~none:(expr unit_val) in 
      Eif (translate_expression e, translate_statements t, f) |> expr ~loc

      | While (e,inv,_v,stmt) -> Ewhile (translate_expression e, [translate_fol inv], [], translate_statements stmt) |> expr ~loc
  in
  List.fold_left (fun x y -> Esequence (expr x,(aux y))) (unit_val) s |> expr


let make_loop (body:Ptree.expr) inv = 
  P.Ewhile (H.expr Etrue,inv,[], body) |> H.expr



(* assume global vars are always int ref for now *)
let generate_declarations (env:env) = let open Ptree in fun (e:expr) ->
  let open H in 
  List.fold_right (fun v decls -> 
    Elet (ident v,false, RKnone, Eapply (expr Eref, econst 0) |> expr, decls) |> expr 
  ) env.env_variables e


let make_setup (s:setup option) = Option.bind s @@ fun s ->
  translate_statements s.setup_body |> Option.some



let translate_program (p : program) : Ptree.mlw_file = 
  let open P in
  let open H in 
  (* let lib =  *)
  (* print_string Env.base_language; *)

  let use_int_Int = H.use ~import:false (["int";"Int"]) in
  let use_ref_Ref = H.use ~import:false (["ref";"Ref"]) in
  let use_option_Option = H.use ~import:false (["option";"Option"]) in
  let use_list_List = H.use ~import:false (["list";"List"]) in
  let use_list_Length = H.use ~import:false (["list";"Length"]) in


  let sp_pre = [translate_formula p.prog_requires] in
  let inv = translate_formula p.prog_ensures in
  let sp_post = [Loc.dummy_position, [pat Pwild, inv]] in
  let spec = Ptree_helpers.{ empty_spec with sp_pre ; sp_post ; sp_diverge = true } in

  let decls = generate_declarations p.prog_env in
  let setup = make_setup p.prog_setup |> fun x -> Option.value x ~default:(expr unit_val)in
  let body = translate_statements p.prog_main.main_body in
  let loop = make_loop body [inv] in

  let stmt = Esequence (Esequence (unit_val |> expr,setup) |> expr, loop) |> expr |> decls in

  let main : decl =   
    Efun ([], None, pat Pwild, Ity.MaskVisible, spec, stmt) 
    |> expr 
    |> fun m ->  Dlet (ident "main", false, Expr.RKnone, m)
  in

  let m = (H.ident "Program", 
    [use_int_Int; use_ref_Ref; use_option_Option; use_list_List; use_list_Length
    ; main
    ]) 
  in Ptree.Modules [m]