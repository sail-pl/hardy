(** Program Syntax *)

open HardyMisc.Utils
open SharedSyntax

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
    
type ('inv, 't, 'decls) program = {
  prog_decls : 'decls;
  prog_setup : ('inv, 't) setup option;
  prog_main : ('inv, 't) main;
}
