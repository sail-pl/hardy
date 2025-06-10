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

let rec fold_expr : type a. ('t expr -> a -> a) -> 't expr -> a -> a =
 fun j e init ->
  match e.value with
  | Int _ | True | False | Var _  -> j e init
  | UnOp (_,e1) -> j e (fold_expr j e1 init)
  | BinOp x -> j e (fold_expr j x.left (fold_expr j x.right init))

let rec map_expr : ('t expr -> 't expr) -> 't expr -> 't expr =
 fun m e ->
  match e.value with
  | Int _ | True | False | Var _ ->  m e
  | UnOp (op,e1) -> m { e with value = UnOp (op,map_expr m e1)}
  | BinOp x ->
      m { e with value = BinOp { x with left=map_expr m x.left; right=map_expr m x.right} }

let expr_vars (e : 't expr) : (string * 't) list -> (string * 't) list =
  fold_expr
    (fun e l -> match e.value with Var (x, t) -> (x, t) :: l | _ -> l)
    e

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
  | While of 't expr * 'inv * unit expr variant * ('inv, 't) stmt list

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

type 'ty env = {
  env_input : 'ty var_decls;
  env_output : 'ty var_decls;
  env_variables : 'ty var_decls;
}
(** program memory environment *)

type ('temp_spec, 'inv, 't) program = {
  prog_decls : base_ty env;
  prog_spec : 'temp_spec list hoare_pair;
  prog_setup : ('inv, 't) setup option;
  prog_main : ('inv, 't) main;
}
