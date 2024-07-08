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

type 'spec hoare_pair = { requires : 'spec; ensures : 'spec }
(** generic hoare requires/ensures pair *)

type ('a, 'spec) hoare_triple = 'a * 'spec hoare_pair

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

type env = {
  env_input : (string * ty) list;
  env_output : (string * ty) list;
  env_variables : (string * ty) list;
}
(** program memory environment *)

type ('temp_spec, 'inv, 'var) program = {
  prog_env : env;
  prog_spec : 'temp_spec list hoare_pair;
  prog_setup : ('inv, 'var) setup option;
  prog_main : ('inv, 'var) main;
}
(** program signature *)

open FOLSyntax
open LTLSyntax (* type 'a triple = string * hoare_pair_t *)

(** type instantiation *)

type inst_spec_t = expr fol
(** instantaneous specification of program expression *)

type temp_spec_t = inst_spec_t ltl
(** ltl logic with fol over program expression *)

type variant_t = { variant : expr }
(** variant expression: only allowed to be a program expression *)

let mk_variant x : variant_t = { variant = x }
let variant x = x.variant

type base_program = (temp_spec_t, inst_spec_t, variant_t) program
