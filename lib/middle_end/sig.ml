(** {1 Middle-end signature}*)

module P = HardyFrontEnd.Syntax.Program
module Cli = HardyFrontEnd.Cli
open HardyFrontEnd.Syntax.Program

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

  val spec_to_input : Cli.info -> P.(temp_spec_t list hoare_pair) -> input
  val exec : Cli.info -> input -> output
  val output_to_automaton : Cli.info -> output -> automaton

  val generate_triples :
    base_program ->
    automaton ->
    (fun_id, P.inst_spec_t list) P.hoare_triple list
end

let translate_spec (type fun_id) (module M : S with type fun_id = fun_id)
    (p : base_program) info : (M.fun_id, inst_spec_t list) P.hoare_triple list =
  M.(
    spec_to_input info p.prog_spec
    |> exec info |> output_to_automaton info |> generate_triples p)
