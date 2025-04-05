(** Program Syntax *)

open HardyMisc.Utils
open SharedSyntax

(* Expressions *)

type 't expr = 't expression_ locatable
(** variables can carry extra information of type ['t] *)

and 't expression_ =
  | Int of int
  | True
  | False
  | Var of string * 't
  | Read of string
  | BinOp of 't expr * arithm_binop * 't expr

(** [private_var x] renames variable id [x] to a name that cannot have been
    declared by the user *)
let private_var = String.cat "_"

let rec fold_expr : type a. ('t expr -> a -> a) -> 't expr -> a -> a =
 fun j e init ->
  match e.value with
  | Int _ | True | False | Var _ | Read _ -> j e init
  | BinOp (e1, _, e2) -> j e (fold_expr j e2 (fold_expr j e1 init))

let rec map_expr : ('t expr -> 't expr) -> 't expr -> 't expr =
 fun m e ->
  match e.value with
  | Int _ | True | False | Var _ | Read _ -> m e
  | BinOp (e1, op, e2) ->
      m { e with value = BinOp (map_expr m e1, op, map_expr m e2) }

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

type ('inv, 'var, 't) stmt = ('inv, 'var, 't) stmt_ locatable
(** program statements *)

and ('inv, 'var, 't) stmt_ =
  | Assign of string * 't expr
  | Emit of 't expr * string
  | If of
      't expr * ('inv, 'var, 't) stmt list * ('inv, 'var, 't) stmt list option
  | While of 't expr * 'inv * 'var * ('inv, 'var, 't) stmt list

type ('inv, 'var, 't) setup = {
  setup_ensures : 'inv list;
  setup_body : ('inv, 'var, 't) stmt list;
}
(** setup routine signature *)

type ('inv, 'var, 't) main = {
  main_loop_inv : 'inv option;
  main_body : ('inv, 'var, 't) stmt list;
}
(** main function signature *)

type 'ty env = {
  env_input : (string * 'ty) list;
  env_output : (string * 'ty) list;
  env_variables : (string * 'ty) list;
}
(** program memory environment *)

type ('temp_spec, 'inv, 'var, 't) program = {
  prog_decls : base_ty env;
  prog_spec : 'temp_spec list hoare_pair;
  prog_setup : ('inv, 'var, 't) setup option;
  prog_main : ('inv, 'var, 't) main;
}
