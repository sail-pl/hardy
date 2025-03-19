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
  type in_ty
  type in_pgrm = (in_ty temp_spec_t, in_ty inst_spec_t, variant_t) program
  type out_pgrm
  type out_decl
  type fun_id
  type in_spec = in_ty inst_spec_t list hoare_pair
  type out_spec
  type in_setup = (in_ty inst_spec_t, variant_t) setup option
  type out_setup
  type in_body = (in_ty inst_spec_t, variant_t) stmt list
  type out_body
  type in_fun = (fun_id, in_ty inst_spec_t list) hoare_triple
  type out_fun

  val generate_declarations : base_ty env -> out_decl list
  val generate_setup : in_setup -> out_setup
  val generate_body : in_body -> out_body
  val generate_spec : in_spec -> out_spec
  val generate_function : fun_id -> out_spec -> out_body -> out_fun
  val generate_program : out_decl list -> out_setup -> out_fun list -> out_pgrm
  val write_program : string -> out_pgrm -> unit
end

module F (B : S) = struct
  let translate_program (p : B.in_pgrm) (triples : B.in_fun list) : B.out_pgrm =
    let decls = B.generate_declarations p.prog_decls in
    let setup = B.generate_setup p.prog_setup in
    let body = B.generate_body p.prog_main.main_body in
    let f : B.in_fun -> B.out_fun =
     fun (id, spec) -> B.generate_function id (B.generate_spec spec) body
    in
    let funs = List.map f triples in
    B.generate_program decls setup funs

  let write_program = B.write_program
end
