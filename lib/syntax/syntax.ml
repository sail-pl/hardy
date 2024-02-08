type binop = 
  | Add | Sub 
  | Mul | Div 
  | Gt | Lt | Gte | Lte
  | Eq 

type expr =
  | Int of int
  | True
  | False
  | Var of string
  | Read of string
  | BinOp of expr * binop * expr

type fol = 
  | FOL_True 
  | FOL_Not of fol
  | FOL_Or of fol * fol 
  | FOL_False 
  | Pred of expr
  | And of fol * fol 
  | Imp of fol * fol 
  | Forall of string * fol 
  | Exists of string * fol



type pltl = 
  | PLTL_True
  | PLTL_Not of pltl
  | PLTL_Or of pltl * pltl
  | Once of pltl
  | Yesterday of pltl
  | Since of pltl * pltl
  | Historically of pltl


type formula = FOL of fol | PLTL of pltl


type invariant = fol 
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
  setup_ensures : ensures option;
  setup_body:stmt list
}

type main = {
  main_invariant : invariant option;
  main_body:stmt list
}

type program = { 
  prog_env : env;
  prog_requires : requires;
  prog_ensures : ensures;
  prog_setup : setup option;
  prog_main : main;
}