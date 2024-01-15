type expr =
  | Int of int
  | Var of string
  | Read of string
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Eq of expr * expr
  | Gt of expr * expr
  | Lt of expr * expr
  | Gte of expr * expr
  | Lte of expr * expr

type formula = 
  | True 
  | False 
  | Pred of expr
  | Not of formula
  | And of formula * formula 
  | Or of formula * formula 
  | Imp of formula * formula 
  | Forall of string * formula 
  | Exists of string * formula

type invariant = formula 
type variant = expr 
type requires = formula 
type ensures = formula 

type stmt =
  | Assign of string * expr
  | Emit of string * expr
  | If of expr * stmt list * stmt list option
  | While of expr * invariant * variant * stmt list

type env = {
  env_input : string list; 
  env_output : string list; 
  env_variables : string list
  }

type setup = {
  setup_ensures : ensures;
  setup_body:stmt list
  }
type main = {
  main_invariant : invariant;
  main_body:stmt list
  }

type program = 
  { 
    prog_env : env;
    prog_requires : requires;
    prog_ensures : ensures;
    prog_setup : setup option;
    prog_main : main;
  }