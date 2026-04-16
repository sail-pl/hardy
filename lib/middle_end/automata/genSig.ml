(** {1 Middle-end signature}*)

module Cli = HardyFrontEnd.Cli
open HardyFrontEnd.Syntax


module type TriplesSig = sig
  type automaton 
  (** input *)

  type t 
  (** output *)

  type local_spec
  type temp_spec 

  val generate_triples : (temp_spec, 'a, local_spec, 'b, 'c) Program.program -> automaton -> t
end



(** The middle-end requires :

    + translation of the specification to a format understandable by the
      external tool
    + execution of the external tool on the specification
    + transformation of the external tool output to an automaton
    + generation of hoare triples based on the program and its automaton
      representation *)
module type S = sig
  type tool_input
  (** external tool input *)

  type tool_output
  (** external tool output *)

  type temp_spec
  type local_spec

  type automaton
  (** internal automaton type *)

  type in_program = (temp_spec, unit, local_spec, Shared.ty , Shared.ty Program.env) Program.program

  val spec_to_input : Cli.info -> temp_spec list Program.hoare_pair -> tool_input
  val exec : Cli.info -> tool_input -> tool_output
  val output_to_automaton : Cli.info -> tool_output -> automaton
end

let translate_spec (type triples automaton temp_spec local_spec)
    (module M : S with type automaton = automaton and type temp_spec = temp_spec and type local_spec = local_spec)
    (module T : TriplesSig with type t = triples and type automaton = automaton and type temp_spec = temp_spec and type local_spec = local_spec) info (p : M.in_program) : T.t =
  M.(
    spec_to_input info p.prog_spec.value
    |> exec info |> output_to_automaton info |> T.generate_triples p)
