(** {1 Middle-end signature}*)

module Cli = HardyFrontEnd.Cli
open HardyFrontEnd.Syntax.Program
open FrontParser.Program

(** The middle-end requires :

    + translation of the specification to a format understandable by the
      external tool
    + execution of the external tool on the specification
    + transformation of the external tool output to an automaton
    + generation of hoare triples based on the program and its automaton
      representation *)
module type S = sig
  type input
  (** external tool input *)

  type output
  (** external tool output *)

  type automaton
  (** internal automaton type *)

  type fun_id
  type ty
  type in_program = (ty temp_spec_t, ty inst_spec_t, variant_t) program

  val spec_to_input : Cli.info -> ty temp_spec_t list hoare_pair -> input
  val exec : Cli.info -> input -> output
  val output_to_automaton : Cli.info -> output -> automaton

  val generate_triples :
    in_program -> automaton -> (fun_id, ty inst_spec_t list) hoare_triple list
end

let translate_spec (type fun_id) (type out_ty)
    (module M : S with type fun_id = fun_id and type ty = out_ty) info
    (p : M.in_program) : (M.fun_id, M.ty inst_spec_t list) hoare_triple list =
  M.(
    spec_to_input info p.prog_spec
    |> exec info |> output_to_automaton info |> generate_triples p)
