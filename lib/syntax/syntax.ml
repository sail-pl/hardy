(*type loc = Lexing.position * Lexing.position
  type 'v locatable  = {loc : loc option; value : 'v}
  let dummy_pos : loc = Lexing.dummy_pos,Lexing.dummy_pos
  let mk_locatable loc value = {loc;value}
  let mk_dummy_loc value = {value;loc=None} *)

open Locations
(* Types *)

type ty = Ty_Int | Ty_Bool

(* Expressions *)
type arithm_binop = Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq

type expr = expression_ locatable

and expression_ =
  | Int of int
  | True
  | False
  | Var of string
  (* | Old of string *)
  | Read of string
  | BinOp of expr * arithm_binop * expr

type common_logic_unary = Not

type common_logic_binary =
  | Xor
  | Equiv
  | Or
  | And
  | Arrow
  | Arithm of arithm_binop

(* FOL *)

type fol = fol_ locatable

and fol_ =
  | FOL_True
  | FOL_False
  | Pred of expr
  | FOL_Unary of common_logic_unary * fol
  | FOL_Binary of fol * common_logic_binary * fol
  | Forall of (string * ty) list * fol
  | Exists of (string * ty) list * fol

(* LTL *)

type ltl_unary =
  | LTL_UArithm of common_logic_unary
  | Next
  | WeakNext
  | Always
  | Eventually

type ltl_binary =
  | LTL_BArithm of common_logic_binary
  | Until
  | WeakUntil
  | Release
  | StrongRelease

type ltl = ltl_ locatable

and ltl_ =
  | LTL_True
  | LTL_False
  | LTL_Pred of fol
  | LTL_Unary of ltl_unary * ltl
  | LTL_Binary of ltl * ltl_binary * ltl

(* PLTL *)

type pltl_unary =
  | PLTL_UArithm of common_logic_unary
  | Once
  | Before
  | Historically

type pltl_binary = PLTL_BArithm of common_logic_binary | Since

type pltl = pltl_ locatable

and pltl_ =
  | PLTL_True
  | PLTL_False
  | PLTL_Pred of fol
  | PLTL_Unary of pltl_unary * pltl
  | PLTL_Binary of pltl * pltl_binary * pltl

(* PROGRAM *)

type formula = FOL of fol | PLTL of pltl | LTL of ltl
type invariant = fol
type variant = expr
type requires = formula
type ensures = formula
type 'a hoare_pair = { requires : 'a; ensures : 'a }

type stmt = stmt_ locatable

and stmt_ =
  | Assign of string * expr
  | Emit of string * expr
  | If of expr * stmt list * stmt list option
  | While of expr * invariant * variant * stmt list

type env = {
  env_input : (string * ty) list;
  env_output : (string * ty) list;
  env_variables : (string * ty) list;
}

type setup = { setup_ensures : fol option; setup_body : stmt list }
type main = { main_invariant : invariant option; main_body : stmt list }

type program = {
  prog_env : env;
  prog_spec : formula option hoare_pair;
  prog_setup : setup option;
  prog_main : main;
}
