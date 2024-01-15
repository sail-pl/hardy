(* open ArduinoSyntax.Syntax
open Why3.Syntax *)

(* type program = 
  { 
    prog_env : env;
    prog_requires : requires;
    prog_ensures : ensures;
    prog_setup : setup option;
    prog_main : main;
  } *)

let translate_env (e : ArduinoSyntax.Syntax.env) : (Why3.Syntax.ident * Why3.Syntax.expr) list =
  (List.map (fun x -> (x,Why3.Syntax.Econst (Some 0))) e.env_input)@
  (List.map (fun x -> (x,Why3.Syntax.Econst (Some 0))) e.env_output)@
  (List.map (fun x -> (x,Why3.Syntax.Econst (Some 0))) e.env_variables)

let rec translate_expr (e : ArduinoSyntax.Syntax.expr) : Why3.Syntax.expr = 
  match e with 
    | Int n -> Econst (Some n) 
    | Var x -> Eident x 
    | Read x -> Eident x 
    | Add (e1, e2) -> Einfix (translate_expr e1, "+",translate_expr e2)
    | Sub (e1, e2) -> Einfix (translate_expr e1, "-",translate_expr e2)
    | Mul (e1, e2) -> Einfix (translate_expr e1, "*",translate_expr e2)
    | Div (_e1, _e2) -> failwith "not supported"
    | Eq (e1, e2) -> Einfix (translate_expr e1, "=",translate_expr e2)
    | Lt (e1, e2) -> Einfix (translate_expr e1, "<",translate_expr e2)
    | Gt (e1, e2) -> Einfix (translate_expr e1, ">",translate_expr e2)
    | Lte (e1, e2) -> Einfix (translate_expr e1, "<=",translate_expr e2)
    | Gte (e1, e2) -> Einfix (translate_expr e1, ">=",translate_expr e2)

    (* type term = 
    | Ttrue 
    | Tfalse 
    | Tconst of constant 
    | Tident of qualid 
    | Tidapp of qualid * term list 
    | Tapply of term * term 
    | Tinfix of term * ident * term 
    | Tbinop of term * binop * term 
    | TAnd of term * term 
    | TOr of term * term
    | TImp of term * term
    | Tnot of term 
    | TForall of binder list * term 
    | TExists of binder list * term *)

let rec translate_expr_to_term (e : ArduinoSyntax.Syntax.expr) : Why3.Syntax.term = 
  match e with 
  | Int n -> Tconst (Some n) 
  | Var x -> Tident x 
  | Read x -> Tident x 
  | Add (e1, e2) -> Tinfix (translate_expr_to_term e1, "+",translate_expr_to_term e2)
  | Sub (e1, e2) -> Tinfix (translate_expr_to_term e1, "-",translate_expr_to_term e2)
  | Mul (e1, e2) -> Tinfix (translate_expr_to_term e1, "*",translate_expr_to_term e2)
  | Div (_e1, _e2) -> failwith "not supported"
  | Eq (e1, e2) -> Tinfix (translate_expr_to_term e1, "=",translate_expr_to_term e2)
  | Lt (e1, e2) -> Tinfix (translate_expr_to_term e1, "<",translate_expr_to_term e2)
  | Gt (e1, e2) -> Tinfix (translate_expr_to_term e1, ">",translate_expr_to_term e2)
  | Lte (e1, e2) -> Tinfix (translate_expr_to_term e1, "<=",translate_expr_to_term e2)
  | Gte (e1, e2) -> Tinfix (translate_expr_to_term e1, ">=",translate_expr_to_term e2)

  let rec translate_formula (f : ArduinoSyntax.Syntax.formula) : Why3.Syntax.term =
    match f with 
      | True -> Ttrue
      | False -> Tfalse 
      | Pred e -> translate_expr_to_term e
      | Not f -> Tnot (translate_formula f)
      | And (f1, f2) -> TAnd (translate_formula f1, translate_formula f2)
      | Or (f1, f2) -> TOr (translate_formula f1, translate_formula f2)
      | Imp (f1, f2) -> TImp (translate_formula f1, translate_formula f2)
      | Forall (x, f) -> TForall ([([x],PTtyapp("int",[]))], translate_formula f)
      | Exists (x, f) -> TForall ([([x],PTtyapp("int",[]))], translate_formula f)

  let rec translate_stmt (s : ArduinoSyntax.Syntax.stmt) : Why3.Syntax.expr =
  match s with 
    | Assign (x, e) -> Eassign (Eident x, None, translate_expr e)
    | Emit (x, e) -> Eassign (Eident x, None, translate_expr e)
    | If(e,s1,Some s2) -> 
        Eif (translate_expr e, translate_stmt_list s1, translate_stmt_list s2)
    | If(e,s1, None) -> 
        Eif (translate_expr e, translate_stmt_list s1, Econst None)
    | While (e,i,v,s) -> 
        EWhile (translate_expr e, [translate_formula i], [translate_expr_to_term v], translate_stmt_list s)
  and translate_stmt_list l = 
    match l with 
      | [] -> failwith "empty list"
      | [s] -> translate_stmt s
      | s::l -> Esequence (translate_stmt s, translate_stmt_list l)

let rec statement_of_statement_list (l : Why3.Syntax.expr list) : Why3.Syntax.expr = 
  match l with 
    | [] -> Econst None 
    | e::l -> Esequence (e, statement_of_statement_list l)


let translate_program (p : ArduinoSyntax.Syntax.program) : Why3.Syntax.why3module =
  {
    m_types = [];
    m_logic = [];
    m_let = translate_env p.prog_env;
    m_rec = 
      let s1 : Why3.Syntax.expr = 
        match p.prog_setup with 
          | None -> Econst None
          | Some s -> translate_stmt_list s.setup_body
      in 
      let s2 = 
          translate_stmt_list p.prog_main.main_body 
      in
      [{
        fun_id = "main";
        fun_params = [];
        fun_spec = {sp_pre= Ttrue; sp_post= Tfalse};
        fun_body = Esequence(s1,s2)
      }]
  }
