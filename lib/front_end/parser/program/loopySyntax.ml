(** Program Syntax *)

open HardyMisc.Utils
open SharedSyntax

type ('inv, 't) stmt = ('inv, 't) stmt_ locatable

and ('inv, 't) stmt_ =
  | Assign of 't expr * 't expr
  | Emit of 't expr * string
  | If of
      't expr * ('inv, 't) stmt list * ('inv, 't) stmt list option
  | While of 't expr * 'inv * 't expr variant * ('inv, 't) stmt list


let map_stmt (type e1 e2) (m_expr : e2 expr -> e2 expr) (m_var : string * e1 -> string * e2) (m_emit: string -> string) (m_fol: 't1 -> 't2)  (s : _ stmt) : _ stmt = 
  let rec aux s = match s.value with 
  | Assign (e1, e2) -> {s with value=Assign (map_expr m_expr m_var e1, map_expr m_expr m_var e2)}
  | Emit (e, id) -> {s with value=Emit (map_expr m_expr m_var e, m_emit id)}
  | If (e, s1, s2) -> {s with value=If (map_expr m_expr m_var e, List.map aux s1, Option.map (List.map aux) s2) }
  | While (e, inv, var, body) -> {s with value=While (map_expr m_expr m_var e, m_fol inv, mk_variant (map_expr m_expr m_var var.variant), List.map aux body)}
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
    
type ('temp_spec, 'spec_data, 'inv, 't, 'decls) program = {
  prog_decls : 'decls;
  prog_spec : ('temp_spec list,'spec_data) hoare_triple;
  prog_setup : ('inv, 't) setup option;
  prog_main : ('inv, 't) main;
}
