open ArduinoSyntax.Syntax
open Why3

module H = Ptree_helpers
module P = Ptree

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
    begin
    match get_binding_type s with
    | Input,_ -> H.([s] |> qualid |> evar)
    | Var,_ | Output,_ -> let deref = H.qualid [Ident.op_prefix "!"] in 
      H.eapp ~loc deref H.[[s] |> qualid |> evar]
    end
    
  | Read s -> Ptree.Easref (H.qualid [s]) |> H.expr ~loc

  | BinOp (e1,binop,e2) -> H.eapp ~loc (translate_binop binop) [translate_expression e1; translate_expression e2]


let rec translate_term ({value=t;loc}:expr) : Ptree.term =
  let loc = Loc.extract loc in 
  match t with
  | True -> H.term ~loc Ttrue
  | False -> H.term ~loc Tfalse
  | Int n -> H.tconst ~loc n
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
    let loc = Loc.extract loc in match s with
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


(* fixme: assumes everything is int for now (easy to change that) *)
let generate_declarations (env:env) = 
  let open P in 
  let open H in 
  let get_exp ty = let ty = match ty with Ty_Bool -> "bool" | Ty_Int -> "int" in 
  Eany ([],RKnone,(Some (PTtyapp ((qualid [ty]),[]))),pat Pwild,MaskVisible,empty_spec) |> expr
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

