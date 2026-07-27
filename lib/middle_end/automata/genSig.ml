module Cli = HardyFrontEnd.Cli
open HardyFrontEnd.Syntax



module type S = sig
  type tool_input
  type tool_output
  type automaton

  type temp_spec
  type spec_data
  type in_pgrm
  include HardyMisc.Utils.PIPELINE with 
    type in_t = (temp_spec, spec_data, in_pgrm) Shared.prog_with_spec and 
    type out_t = (temp_spec, spec_data,in_pgrm) Shared.prog_with_spec


  val spec_to_input : Cli.config -> temp_spec list Shared.hoare_pair -> tool_input
  val exec : Cli.config -> tool_input -> tool_output
  val output_to_automaton : Cli.config -> tool_output -> automaton
end

module type TriplesSig = sig
  include HardyMisc.Utils.PIPELINE 


  type automaton 

  val generate_triples : in_t -> automaton -> out_t
end




let translate_spec (type triples automaton temp_spec spec_data in_pgrm)
    (module M : S with type automaton = automaton and type temp_spec = temp_spec and type spec_data = spec_data and type in_pgrm = in_pgrm)
    (module T : TriplesSig with type in_t = M.out_t and type out_t = triples and type automaton = automaton) config (p : M.out_t) : T.out_t =
  M.(
    spec_to_input config p.prog_spec.value
    |> exec config |> output_to_automaton config |> T.generate_triples p)
