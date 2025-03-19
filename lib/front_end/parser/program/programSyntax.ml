(** Program Syntax *)

open HardyMisc.Utils
open SharedSyntax

(* Expressions *)

type expr = expression_ locatable

and expression_ =
  | Int of int
  | True
  | False
  | Var of string
  | Prev of string
  | Read of string
  | BinOp of expr * arithm_binop * expr

(** [private_var x] renames variable id [x] to a name that cannot have been
    declared by the user *)
let private_var = String.cat "_"

let rec fold_expr : type a. (expr -> a -> a) -> expr -> a -> a =
 fun j e init ->
  match e.value with
  | Int _ | True | False | Var _ | Prev _ | Read _ -> j e init
  | BinOp (e1, _, e2) -> j e (fold_expr j e2 (fold_expr j e1 init))

let rec map_expr : (expr -> expr) -> expr -> expr =
 fun m e ->
  match e.value with
  | Int _ | True | False | Var _ | Prev _ | Read _ -> m e
  | BinOp (e1, op, e2) ->
      m { e with value = BinOp (map_expr m e1, op, map_expr m e2) }

let expr_vars : expr -> string list -> string list =
  fold_expr (fun e l -> match e.value with Var x -> x :: l | _ -> l)

type 'spec hoare_pair = { requires : 'spec; ensures : 'spec }
(** generic hoare requires/ensures pair *)

type ('a, 'spec) hoare_triple = 'a * 'spec hoare_pair
type 'v variant = { variant : 'v }

let mk_variant x : _ variant = { variant = x }
let variant x = x.variant

type ('inv, 'var) stmt = ('inv, 'var) stmt_ locatable
(** program statements *)

and ('inv, 'var) stmt_ =
  | Assign of string * expr
  | Emit of expr * string
  | If of expr * ('inv, 'var) stmt list * ('inv, 'var) stmt list option
  | While of expr * 'inv * 'var * ('inv, 'var) stmt list

type ('inv, 'var) setup = {
  setup_ensures : 'inv list;
  setup_body : ('inv, 'var) stmt list;
}
(** setup routine signature *)

type ('inv, 'var) main = {
  main_loop_inv : 'inv option;
  main_body : ('inv, 'var) stmt list;
}
(** main function signature *)

type 'ty env = {
  env_input : (string * 'ty) list;
  env_output : (string * 'ty) list;
  env_variables : (string * 'ty) list;
}
(** program memory environment *)

type ('temp_spec, 'inv, 'var) program = {
  prog_decls : base_ty env;
  prog_spec : 'temp_spec list hoare_pair;
  prog_setup : ('inv, 'var) setup option;
  prog_main : ('inv, 'var) main;
}

type 's fun_id = { id : 's }
