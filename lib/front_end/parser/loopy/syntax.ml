(** Program Syntax *)

open HardyMisc.Utils
open SharedSyntax

type ('inv, 't) stmt = ('inv, 't) stmt_ locatable

and ('inv, 't) stmt_ =
  | Assign of (unit,'t) expr * (unit,'t) expr
  | Emit of (unit,'t) expr * string
  | If of
      (unit,'t) expr * ('inv, 't) stmt list * ('inv, 't) stmt list option
  | While of (unit,'t) expr * 'inv * (unit,'t) expr variant * ('inv, 't) stmt list


let map_stmt (type e1 e2) (m_expr : (unit,e2) expr -> (unit,e2) expr) (m_var : string * e1 -> string * e2) (m_emit: string -> string) (m_fol: 't1 -> 't2)  (s : _ stmt) : _ stmt = 
  let map_expr = map_expr Fun.id m_expr m_var in 
  let rec aux s = match s.value with 
  | Assign (e1, e2) -> {s with value=Assign (map_expr e1, map_expr e2)}
  | Emit (e, id) -> {s with value=Emit (map_expr e, m_emit id)}
  | If (e, s1, s2) -> {s with value=If (map_expr e, List.map aux s1, Option.map (List.map aux) s2) }
  | While (e, inv, var, body) -> {s with value=While (map_expr e, m_fol inv, mk_variant (map_expr  var.variant), List.map aux body)}
  in aux s


type 'ty var_decls = (string * 'ty) list

type ('inv, 't) setup = {
  setup_ensures : 'inv list;
  setup_body : ('inv, 't) stmt list;
}

type ('inv, 't) main = {
  main_loop_inv : 'inv list;
  main_body : ('inv, 't) stmt list;
}


type parsed_env = {
  env_input : base_ty var_decls;
  env_output : base_ty var_decls;
  env_variables : base_ty var_decls;
}

type 'ty env = {
  env_variables : 'ty Bindings.t;
}
    
type ('inv, 't, 'decls) program = {
  prog_decls : 'decls;
  prog_setup : ('inv, 't) setup option;
  prog_main : ('inv, 't) main;
}
