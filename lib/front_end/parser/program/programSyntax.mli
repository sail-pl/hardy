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
  | Real of {radix:int ; num:string ; frac:string  ; exp:string option}
  | True
  | False
  | Var of string * 't
  | UnOp of expr_uop * 't expr
  | BinOp of {left: 't expr ; op: expr_binop ; right : 't expr}
  | ArrayCell of {array: 't expr; idx: 't expr}
  | Array of 't expr iarray
  | String of string
  | Prod of 't expr list

(** [private_var x] renames variable id [x] to a name that cannot have been
    declared by the user *)
val pp_private : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit

val private_var : string -> string

val fold_expr : ('a -> 't expr -> 'a) -> 'a ->'t expr -> 'a


val map_expr : ('t2 expr -> 't2 expr) -> (string * 't1 -> string * 't2) -> 't1 expr -> 't2 expr 

  
val expr_vars : (string * 't) list -> 't expr -> (string * 't) list

type 'spec hoare_pair = { requires : 'spec; ensures : 'spec }

type ('spec, 'data) hoare_triple = ('spec hoare_pair, 'data) labeled

val map_triple_data : ('a -> 'b) -> ('c, 'a) labeled -> ('c, 'b) labeled

(** generic hoare requires/ensures pair *)

type 'v variant = { variant : 'v }

val variant : 'a variant -> 'a 

val mk_variant : 'a -> 'a variant

(** program statements *)
type ('inv, 't) stmt = ('inv, 't) stmt_ locatable
and ('inv, 't) stmt_ =
  | Assign of 't expr * 't expr
  | Emit of 't expr * string
  | If of
      't expr * ('inv, 't) stmt list * ('inv, 't) stmt list option
  | While of 't expr * 'inv * 't expr variant * ('inv, 't) stmt list


val map_stmt : ('e2 expr -> 'e2 expr) -> (string * 'e1 -> string * 'e2) -> (string -> string) -> ('t1 -> 't2)  -> ('t1,'e1) stmt -> ('t2,'e2) stmt 


type 'ty var_decls = (string * 'ty) list

type ('inv, 't) setup = {
  setup_ensures : 'inv list;
  setup_body : ('inv, 't) stmt list;
}
(** setup routine signature *)

type ('inv, 't) main = {
  main_loop_inv : 'inv list;
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
    
type ('temp_spec, 'spec_data, 'inv, 't, 'decls) program = {
  prog_decls : 'decls;
  prog_spec : ('temp_spec list,'spec_data) hoare_triple;
  prog_setup : ('inv, 't) setup option;
  prog_main : ('inv, 't) main;
}
