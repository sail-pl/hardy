(** Program Syntax *)

open HardyMisc.Utils
open SharedSyntax


type 't obby_expr_  = 
  | Call of string * ('t obby_expr_, 't) expr list
and 't obby_expr = ('t obby_expr_, 't) expr


let rec obby_map_expr : type t1 t2. (t2 obby_expr -> t2 obby_expr) -> (string * t1 -> string * t2) -> t1 obby_expr -> t2 obby_expr =
  fun m var_map e -> map_expr (function Call (id,args) -> Call (id, List.map (obby_map_expr m var_map) args)) m var_map e

(* m { e with value= Ext (Call (id, List.map obby_map_expr args))} *)

type ('inv, 't) stmt = ('inv, 't) stmt_ locatable

and ('inv, 't) stmt_ =
  | Assign of 't obby_expr * 't obby_expr
  | Invoke of string * 't obby_expr list
  | If of
      't obby_expr * ('inv, 't) stmt list * ('inv, 't) stmt list option
  | While of 't obby_expr * 'inv * 't obby_expr variant * ('inv, 't) stmt list

  

let map_stmt (type e1 e2) (m_expr1 : e2 obby_expr -> e2 obby_expr) (m_expr2 : ('t,e2) expr -> ('t,e2) expr) (m_var : string * e1 -> string * e2) (m_invoke: string -> string) (m_fol: 't1 -> 't2)  (s : _ stmt) : _ stmt = 
  let rec aux s = match s.value with 
  | Assign (e1, e2) -> {s with value=Assign (obby_map_expr m_expr1 m_var e1, obby_map_expr m_expr1 m_var e2)}
  | Invoke (id,args) -> {s with value=Invoke (m_invoke id, List.map (obby_map_expr m_expr1  m_var) args )}
  | If (e, s1, s2) -> {s with value=If (obby_map_expr m_expr1  m_var e, List.map aux s1, Option.map (List.map aux) s2) }
  | While (e, inv, var, body) -> {s with value=While (obby_map_expr m_expr1  m_var e, m_fol inv, mk_variant (obby_map_expr m_expr1  m_var var.variant), List.map aux body)}
  in aux s


type 'ty var_decls = (string * 'ty) list

type ('temp_spec, 'inst_spec) node_spec_t = {
  (* n_requires : 'temp_spec list;
  n_ensures : 'temp_spec list;  *)
  node_guarantees : 'inst_spec list;
  node_assumes : 'temp_spec list;
}

type ('inv, 't) func = {
  f_name : string;
  f_requires : 'inv list;
  f_ensures : 'inv list ;
  f_args : string list ;
  f_body : ('inv, 't) stmt list;
}

type 'inst_spec node = {
  node_id : string;
  node_rtype : base_ty var_decls;
  node_params : base_ty var_decls;
  node_vars : base_ty var_decls;
  node_preamble : ('inst_spec, unit) stmt list;
  node_body :  ('inst_spec, unit) stmt list;
  node_funs : ('inst_spec, unit) func list
}
type parsed_env = {
  env_input : base_ty var_decls;
  env_output : base_ty var_decls;
  env_variables : base_ty var_decls;
}

type 'ty env = {
  env_variables : 'ty Bindings.t;
}
    
let init_node = "main"

let find_node l id = List.find (fun n -> n.node_id = id) l
let find_start_node l = find_node l init_node

type ('temp,'inv) program = ('temp,unit, ('inv node)) prog_with_spec list
