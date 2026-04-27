module Cli = HardyFrontEnd.Cli
open HardyFrontEnd.Syntax


module type TriplesSig = sig
  type automaton 

  type t 

  type local_spec
  type temp_spec 

  val generate_triples : (temp_spec, 'a, local_spec, 'b, 'c) Program.program -> automaton -> t
end




module type S = sig
  type tool_input
  type tool_output
  type temp_spec
  type local_spec
  type automaton
  type in_program = (temp_spec, unit, local_spec, Shared.ty , Shared.ty Program.env) Program.program

  val spec_to_input : Cli.config -> temp_spec list Program.hoare_pair -> tool_input
  val exec : Cli.config -> tool_input -> tool_output
  val output_to_automaton : Cli.config -> tool_output -> automaton
end

let translate_spec (type triples automaton temp_spec local_spec)
    (module M : S with type automaton = automaton and type temp_spec = temp_spec and type local_spec = local_spec)
    (module T : TriplesSig with type t = triples and type automaton = automaton and type temp_spec = temp_spec and type local_spec = local_spec) config (p : M.in_program) : T.t =
  M.(
    spec_to_input config p.prog_spec.value
    |> exec config |> output_to_automaton config |> T.generate_triples p)
