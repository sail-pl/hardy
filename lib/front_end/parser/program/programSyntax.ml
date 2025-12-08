(** Program Syntax *)

open HardyMisc.Utils
open SharedSyntax

(* Expressions *)

type expr_uop = ENot
type expr_binop = Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq | Neq | EAnd | EOr

type 't expr = 't expression_ locatable
(** variables can carry extra information of type ['t] *)

and 't expression_ =
  | Int of int
  | True
  | False
  | Var of string * 't
  | UnOp of expr_uop * 't expr
  | BinOp of {left: 't expr ; op: expr_binop ; right : 't expr}

(** [private_var x] renames variable id [x] to a name that cannot have been
    declared by the user *)
let private_var = String.cat "_"

let rec fold_expr : type a. (a -> 't expr -> a) -> a ->'t expr -> a =
 fun j init e ->
  match e.value with
  | Int _ | True | False | Var _  -> j init e
  | UnOp (_,e1) -> j (fold_expr j init e1 ) e
  | BinOp x -> j (fold_expr j (fold_expr j init x.right) x.left) e 

let rec map_expr : type t1 t2. (t2 expr -> t2 expr) -> (string * t1 -> string * t2) -> t1 expr -> t2 expr =
 fun m var_map e ->
  match e.value with
  | Int _ | True | False as value -> m {e with value}
  | Var (id,v) -> let (id,v) = var_map (id,v) in m {e with value=Var (id,v)}
  | UnOp (op,e1) -> m { e with value = UnOp (op,map_expr m var_map e1)}
  | BinOp x ->
      m { e with value = BinOp { x with left=map_expr m var_map x.left; right=map_expr m var_map x.right} }

let expr_vars : (string * 't) list -> 't expr -> (string * 't) list = fun x -> 
  fold_expr (fun l e -> match e.value with Var (x, t) -> (x, t) :: l | _ -> l) x

type 'spec hoare_pair = { requires : 'spec; ensures : 'spec }
(** generic hoare requires/ensures pair *)

type ('a, 'spec) hoare_triple = 'a * 'spec hoare_pair
type 'v variant = { variant : 'v }

let mk_variant x : _ variant = { variant = x }
let variant x = x.variant

type ('inv, 't) stmt = ('inv, 't) stmt_ locatable
(** program statements *)

and ('inv, 't) stmt_ =
  | Assign of 't expr * 't expr
  | Emit of 't expr * string
  | If of
      't expr * ('inv, 't) stmt list * ('inv, 't) stmt list option
  | While of 't expr * 'inv * 't expr variant * ('inv, 't) stmt list


let map_stmt (type e1 e2) (m_expr : e2 expr -> e2 expr) (m_var : string * e1 -> string * e2) (m_fol: 't1 -> 't2) (s : _ stmt) : _ stmt = 
let rec aux s = match s.value with 
| Assign (e1, e2) -> {s with value=Assign (map_expr m_expr m_var e1, map_expr m_expr m_var e2)}
| Emit (e, id) -> {s with value=Emit (map_expr m_expr m_var e, id)}
| If (e, s1, s2) -> {s with value=If (map_expr m_expr m_var e, List.map aux s1, Option.map (List.map aux) s2) }
| While (e, inv, var, body) -> {s with value=While (map_expr m_expr m_var e, m_fol inv, mk_variant (map_expr m_expr m_var var.variant), List.map aux body)}
in aux s




type 'ty var_decls = (string * 'ty) list

type ('inv, 't) setup = {
  setup_ensures : 'inv list;
  setup_body : ('inv, 't) stmt list;
}
(** setup routine signature *)

type ('inv, 't) main = {
  main_loop_inv : 'inv option;
  main_body : ('inv, 't) stmt list;
}
(** main function signature *)


(** program memory environment, after parsing but before typechecking *)
type parsed_env = {
  env_input : base_ty var_decls;
  env_output : base_ty var_decls;
  env_variables : base_ty var_decls;
}

(** program memory environment, after typechecking *)
type 'ty env = {
  env_variables : 'ty Bindings.t;
}
    
type ('temp_spec, 'inv, 't, 'decls) program = {
  prog_decls : 'decls;
  prog_spec : 'temp_spec list hoare_pair;
  prog_setup : ('inv, 't) setup option;
  prog_main : ('inv, 't) main;
}
