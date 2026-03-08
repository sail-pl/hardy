(** {1 Back-end signature} *)
open HardyFrontEnd.Syntax
open Shared
open HardyMisc.Utils
open Program

(** The back-end requires:

    _ generation of program declarations from the environment
    - generation of the initialization routine
    - generation of program specification
    - generation of a function's body
    - generation of a function from the body and its specification
    - generation of the program from the declarations, initialization procedure
      and functions *)

(* type spec_info = {loop_invariant: }  *)

module type S = sig
  type local_spec
  type temp_spec 

  type in_pgrm = (temp_spec, unit, local_spec, ty, ty env) Program.program
  type in_setup = (local_spec, ty) setup
  type in_body = (local_spec, ty) stmt list
  type in_fun 
  type in_spec

  type triple_data

  type out_pgrm
  type out_decl
  type out_body
  type out_setup
  type out_fun

  type processed_defs = {
    processed_decls : out_decl list ;
    processed_setup : out_setup option ;
    processed_functions: out_fun list ;
  }

  val reset : unit -> unit
  (** reset the backend state (bindings etc.) *)

  val generate_declarations : ty env -> out_decl list
  val generate_setup : in_setup -> out_setup
  val generate_body : in_body -> out_body
  val generate_function : ((in_spec, out_body) hoare_triple, triple_data) labeled ->  out_fun

  val generate_program : processed_defs -> out_pgrm

  val write_program : string -> out_pgrm -> unit
end

(* fixme: shouldn't require module encapsulation with OCaml >= 5.5 (modular explicits)  *)
module F (B : S) = struct
  let translate_program 
    (p : B.in_pgrm) 
    (triples : ((B.in_spec ,B.in_fun) hoare_triple, B.triple_data) labeled conjunction) 
    : B.out_pgrm =
    B.reset ();
    let processed_decls = B.generate_declarations p.prog_decls
    and processed_setup = Option.map B.generate_setup p.prog_setup
    and processed_functions = 
      let body = B.generate_body p.prog_main.main_body in
      let c = map_conjuncts (map_value (map_triple_data (fun _ -> body)) >> B.generate_function) triples in 
      c.conjuncts
    in
    B.generate_program {processed_setup; processed_functions ; processed_decls}

  let write_program = B.write_program
end
