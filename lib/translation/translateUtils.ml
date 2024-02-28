module S = ArduinoSyntax.Syntax
module AS = ArduinoSyntax.AutomatonSyntax

open Why3
open S

module H = Ptree_helpers
module P = Ptree

let get_loc loc = match loc with None -> Why3.Mlw_printer.next_pos () | Some l -> Loc.extract l 


type info = {file:string; ltl2baPath:string; verbose:bool; pltl_mode:bool; outdir : string}

type id_cat = Var | Input | Output

let bindings : (string,id_cat*ty) Hashtbl.t = Hashtbl.create 100

let add_binding (v,ty) (cat:id_cat)= 
  if Hashtbl.mem bindings v then
    failwith @@ Format.sprintf "variable %s already declared" v
  else 
    Hashtbl.add bindings v (cat,ty)

let get_binding_type v = 
  Hashtbl.find bindings v


let unit_val = Why3.Ptree.Etuple []

let string_of_binop : arithm_binop -> string = function
  | Add -> "+" | Sub -> "-" | Mul -> "*"  | Div -> "/"
  | Gt -> ">"  | Lt -> "<"  | Gte -> ">=" | Lte -> "<="
  | Eq -> "="


let translate_binop op = Ptree_helpers.qualid [Ident.op_infix (string_of_binop op)]

let rec translate_expression ({value=e;loc}:expr) : Ptree.expr = 
  let loc = get_loc loc in 
  match e with
  | True -> H.expr ~loc Etrue
  | False -> H. expr ~loc  Efalse
  | Int n -> H.econst n ~loc
  (* | Old _ -> Loc.(error ~loc @@ Message "Old only allowed inside formulas") *)
  | Var s -> 
    begin
    match get_binding_type s with
    | Input,_ -> H.([s] |> qualid |> evar)
    | Var,_ | Output,_ -> let deref = H.qualid [Ident.op_prefix "!"] in 
      H.eapp ~loc deref H.[[s] |> qualid |> evar]
    end
    
  | Read s -> Ptree.Easref (H.qualid [s]) |> H.expr ~loc

  | BinOp (e1,binop,e2) -> H.eapp ~loc (translate_binop binop) [translate_expression e1; translate_expression e2]


let rec translate_term (e:expr) : Ptree.term =
  let loc = get_loc e.loc in 
  match e.value with
  | True -> H.term ~loc Ttrue
  | False -> H.term ~loc Tfalse
  | Int n -> H.tconst ~loc n
  (* | Old s -> 	H.term ~loc H.(Tat (translate_term {value=Var s;loc=e.loc},ident ~loc Dexpr.old_label)) *)
  | Var s ->     
    begin
    match get_binding_type s with
    | Input,_ -> H.([s] |> qualid |> tvar)
    | Var,_ | Output,_ -> let deref = H.qualid [Ident.op_prefix "!"] in 
      H.tapp ~loc deref H.[[s] |> qualid |> tvar]
    end

  | Read s ->       
    Ptree.Tasref (H.qualid [s]) |> H.term ~loc

  | BinOp (e1,binop,e2) -> H.tapp ~loc (translate_binop binop) [translate_term e1; translate_term e2]

  
let rec translate_statements (tr_form : invariant -> P.term) (s: stmt list)  : Ptree.expr = 
  let open P in 
  let open H in 
  let translate_statements = translate_statements tr_form in 
  let aux {value=s;loc} = 
    let loc = get_loc loc in match s with
    | Assign (id, e) ->
      let assgn = qualid [Ident.op_infix ":="] in 
      eapp ~loc assgn [([id] |> qualid |> evar) ; translate_expression e]

    | Emit (id,e) -> Eassign [(translate_expression e, None, ([id] |> qualid |> evar))] |> expr ~loc (* will need to be treated differently *)
    | If (e,t,f) -> 
      let f = Option.fold ~some:translate_statements f ~none:(expr unit_val) in 
      Eif (translate_expression e, translate_statements t, f) |> expr ~loc

      | While (e,inv,_v,stmt) -> Ewhile (translate_expression e, [tr_form inv], [], translate_statements stmt) |> expr ~loc
  in
  List.fold_left (fun x y -> Esequence (expr x,(aux y))) (unit_val) s |> expr


  let string_of_ty = function Ty_Bool -> "bool" | Ty_Int -> "int"


let get_pty ty = 
  let ty = string_of_ty ty in P.(PTtyapp ((H.qualid [ty]),[]))

let generate_declarations (env:env) = 
  let open P in 
  let open H in 
  let get_exp ty = 
    Eany ([],RKnone,(Some (get_pty ty)),pat Pwild,MaskVisible,empty_spec) |> expr
  in

  (* inputs are r *)
  List.fold_right (fun (v,ty) decls -> 
    add_binding (v,ty) Input;
    Dlet (ident v,false, RKnone, get_exp ty) :: decls
  ) env.env_input [] 
  |> (* outputs are rw *)
  List.fold_right (fun (v,ty) decls -> 
    add_binding (v,ty) Output;
    Dlet (ident v,false, RKnone, eapply (expr Eref) (get_exp ty)) :: decls
  ) env.env_output
  |> (* vars are rw *)
  List.fold_right (fun (v,ty) decls -> 
    add_binding (v,ty) Var;
    Dlet (ident v,false, RKnone, eapply (expr Eref) (get_exp ty)) :: decls
  ) env.env_variables

let string_of_unop : common_logic_unary -> string =  function
| Not -> "~"



let string_of_common_logic_binary : common_logic_binary -> string = function
| Xor -> "^"
| Equiv -> "<->"
| Or -> "OR"
| And -> "AND"
| Arrow -> "->"
| Arithm o -> string_of_binop o


let rec string_of_exp (e:expr) : string = match e.value with
  | Int n -> string_of_int n 
  | True -> "true"
  | False -> "false"
  (* | Old s -> Format.sprintf "old(%s)" s *)
  | Var s | Read s -> s
  | BinOp (e1,op,e2) -> Format.sprintf "(%s) %s (%s)" (string_of_exp e1) (string_of_binop op) (string_of_exp e2)

let rec string_of_fol (f : fol) : string = 
  let open Format in 

  let print_idty idty = 
      String.concat " " (
        List.map (fun (id,ty) -> Format.sprintf "(%s:%s)" id (string_of_ty ty)) idty
      ) 
  in

  match f.value with
  | FOL_True -> "true"
  | FOL_False -> "false"
  | Pred e -> string_of_exp e
  | FOL_Unary (op,f) -> sprintf "%s (%s)" (string_of_unop op) (string_of_fol f)
  | FOL_Binary (f1,op,f2) -> sprintf "(%s) %s (%s)" (string_of_fol f1) (string_of_common_logic_binary op) (string_of_fol f2)
  | Forall (idty, f) -> sprintf "forall %s. %s" (print_idty idty) (string_of_fol f)
  | Exists (idty, f) -> asprintf "exists %s. %s" (print_idty idty) (string_of_fol f)



let string_of_ltl_binop : ltl_binary -> string = function
  | Until -> "U"
  | Release -> "R"
  | LTL_BArithm Arrow -> "->"
  | LTL_BArithm Or -> "||"
  | LTL_BArithm And -> "&&"
  | LTL_BArithm Equiv -> "<->"
  | _ -> failwith "unsupported bop"
  
let string_of_ltl_unop : ltl_unary -> string = function
  | Next -> "X"
  | Always -> "G"
  | Eventually -> "F"
  | LTL_UArithm Not -> "!"
  | WeakNext -> failwith "unsupported unop"
  
  

  let string_of_ltl (string_of_pred: fol -> string) : ltl -> string = 
    let rec aux f =
      match f.value with
      | LTL_True -> "true"
      | LTL_False -> "false"
      | LTL_Pred p -> string_of_pred p
      | LTL_Binary (f1,op,f2) -> 
        let f1 = aux f1 in
        let f2 = aux f2 in
        Format.sprintf "(%s) %s (%s)" f1 (string_of_ltl_binop op) f2
      | LTL_Unary (op,f) ->
        let f = aux f in
        Format.sprintf "%s (%s)" (string_of_ltl_unop op) f
    in 
    aux


let rec pterm_of_fol ({value=f;loc}:fol) : Ptree.term = 
  let open H in 
  let open P in 
  let loc = get_loc loc in
  match f with
  | FOL_True -> term ~loc Ttrue
  | FOL_False -> term ~loc Tfalse
  | Pred p -> translate_term p 
  | FOL_Unary (uop,t) -> begin match uop with Not -> Tnot (pterm_of_fol t) |> term ~loc end
  | FOL_Binary (t1,bop,t2) -> 
    let t1 = pterm_of_fol t1 in 
    let t2 = pterm_of_fol t2 in
    let bop = begin match bop with
    | And -> Dterm.DTand
    | Or -> Dterm.DTor
    | Arrow -> Dterm.DTimplies
    | Equiv -> Dterm.DTiff
    | Xor -> failwith "todo xor"
    | Arithm _ -> failwith "todo Arithm"
    end in
    Tbinop (t1, bop, t2) |> term ~loc
  | Forall (v,f) -> Tquant (
      DTforall,  
      List.concat (List.map (fun (v,ty) -> let pty = get_pty ty in one_binder v ~pty) v), 
      [], 
      (pterm_of_fol f)
    ) |> term ~loc
  | Exists (v,f) ->  Tquant (
      DTexists, 
      List.concat (List.map (fun (v,ty) -> let pty = get_pty ty in one_binder v ~pty) v), 
      [], 
      (pterm_of_fol f)
    ) |> term ~loc


let fol_of_bform (convert_atom: string -> fol) = 
  let open AS in

  let rec aux = function
  | True -> mk_dummy_loc FOL_True
  | False -> mk_dummy_loc FOL_False
  | Atom s -> convert_atom s
  | And (s1,s2) -> 
      let s1 = aux s1 in
      let s2 = aux s2 in 
      mk_dummy_loc (FOL_Binary (s1,And,s2))
  | Or (s1,s2) -> 
      let s1 = aux s1 in
      let s2 = aux s2 in 
      mk_dummy_loc (FOL_Binary (s1,Or,s2))
  | Not s -> 
    let s = aux s in
    mk_dummy_loc (FOL_Unary (Not,s))

  in 
  aux


let rec determ_exp (e:expr) : expr =
  let value = 
    match e.value with
    | BinOp (e1,op,e2) -> let e1 = determ_exp e1 and e2 = determ_exp e2 in BinOp (e1,op,e2)
    | _ as x -> x
  in
  {value;loc=None}

(* 2 formulas are equals if they are syntactically the same modulo their position *)
let rec determ_fol (f:fol) : fol = 
    let value = 
      match f.value with 
      | Pred p -> Pred (determ_exp p)
      | FOL_Unary (op,f) -> let f = determ_fol f in FOL_Unary (op,f)
      | FOL_Binary (f1, op, f2) -> 
        let f1 = determ_fol f1 and f2 = determ_fol f2 in FOL_Binary (f1,op,f2)
      | Forall (x,f) -> let f = determ_fol f in Forall (x,f)
      | Exists (x,f) -> let f = determ_fol f in Exists (x,f)
      | _ as x -> x
    in
    {value;loc=None}



module type AtomSig = sig
  val get : string -> string * fol

  val subst: string -> string

  val add : fol -> string * string
end

module Atom() : AtomSig = struct

  (* key is a hash of fol, value is a short name for fol + fol itself*)
  let atomic_bindings : (int, string*fol) Hashtbl.t = Hashtbl.create 100

  let cnt = ref 0

  let get (s:string) = let k = String.(sub s 2 (length s - 2) |> int_of_string) in Hashtbl.find atomic_bindings k 

  let sub_atom_in_str f = 
    let open Str in 
    let r = regexp {|f_\([0-9]+\)|} in
    global_substitute r (fun m -> matched_string m |> f) 


  let subst = sub_atom_in_str (fun s -> 
    let _,inv = get s in
    string_of_fol inv
  )

  let add (f:fol) = 
    let label =  Format.sprintf "f_%i" in 
  
    (* we must get the same atom if the formulas are syntactically equal*)
    let key = Hashtbl.hash (determ_fol f) in 
    
    match Hashtbl.find_opt atomic_bindings key with
    | None -> 
      let short_name = "F" ^ string_of_int !cnt in
      Hashtbl.add atomic_bindings key (short_name,f);
      incr cnt;
      short_name,label key
    | Some (sn,_) ->
        sn,label key
    
end