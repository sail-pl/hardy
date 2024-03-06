(*type loc = Lexing.position * Lexing.position
  type 'v locatable  = {loc : loc option; value : 'v}
  let dummy_pos : loc = Lexing.dummy_pos,Lexing.dummy_pos
  let mk_locatable loc value = {loc;value}
  let mk_dummy_loc value = {value;loc=None} *)

open Locations
open Types
open Operators
open Fol
open Ltl

(* Expressions *)

type expr = expression_ locatable

and expression_ =
  | Int of int
  | True
  | False
  | Var of string
  (* | Old of string *)
  | Read of string
  | BinOp of expr * arithm_binop * expr





(* PLTL *)
(*
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
  | PLTL_Pred of expr fol
  | PLTL_Unary of pltl_unary * pltl
  | PLTL_Binary of pltl * pltl_binary * pltl
*)
(* PROGRAM *)

(* type formula = FOL of expr fol | PLTL of pltl | LTL of ltl *)
type invariant = expr fol
type variant = {var_expr : expr}

type requires = expr fol ltl
type ensures = expr fol ltl

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

type setup = { setup_ensures : expr fol option; setup_body : stmt list }
type main = { main_invariant : invariant option; main_body : stmt list }

type program = {
  prog_env : env;
  prog_spec : expr fol ltl option hoare_pair;
  prog_setup : setup option;
  prog_main : main;
}
