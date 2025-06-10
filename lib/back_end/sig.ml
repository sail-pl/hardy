(** {1 Back-end signature} *)

open HardyFrontEnd.Syntax
open Program
open Shared

(** The back-end requires:

    _ generation of program declarations from the environment
    - generation of the initialization routine
    - generation of program specification
    - generation of a function's body
    - generation of a function from the body and its specification
    - generation of the program from the declarations, initialization procedure
      and functions *)
module type S = sig
  type in_pgrm = base_program

  (* (in_ty temp_spec_t, (in_ty,unit) inst_spec_t, variant_t, unit) program *)
  type fol_data
  type triple_data
  type in_setup = (Shared.ty fol_t, unit) setup
  type in_body = (Shared.ty fol_t, unit) stmt list

  type in_fun =
    ( triple_data,
      (Shared.ty, fol_data) inst_spec_t U.disjunction U.conjunction )
    hoare_triple

  type in_spec = in_fun
  type out_pgrm
  type out_decl
  type out_spec
  type out_body
  type out_setup
  type out_fun

  val generate_declarations : base_ty env -> out_decl list
  val generate_setup : in_setup option -> out_setup option
  val generate_body : in_body -> out_body
  val generate_spec : in_spec -> out_spec
  val generate_function : triple_data -> out_spec -> out_body -> out_fun

  val generate_program :
    out_decl list -> out_setup option -> out_fun list -> out_pgrm

  val write_program : string -> out_pgrm -> unit
end

module F (B : S) = struct
  let translate_program (p : B.in_pgrm) (triples : B.in_fun list) : B.out_pgrm =
    let decls = B.generate_declarations p.prog_decls in
    let setup = B.generate_setup p.prog_setup in
    let body = B.generate_body p.prog_main.main_body in
    let f : B.in_fun -> B.out_fun =
     fun (data, spec) ->
      B.generate_function data (B.generate_spec (data, spec)) body
    in
    let funs = List.map f triples in
    B.generate_program decls setup funs

  let write_program = B.write_program
end
