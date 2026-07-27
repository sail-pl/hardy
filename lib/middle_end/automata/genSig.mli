(** {1 Middle-end signature}*)

open FrontParser.SharedSyntax

module Cli = HardyFrontEnd.Cli

module type TriplesSig =
sig
  include HardyMisc.Utils.PIPELINE 

  type automaton 

  val generate_triples : in_t -> automaton -> out_t
end

(** The middle-end requires:
- translation of the specification to a format understandable by the external tool
- execution of the external tool on the specification
- transformation of the external tool output to an automaton
- generation of hoare triples based on the program and its automaton
    representation 
*)
module type S =
sig
    type tool_input  
    (** external tool input *)

    type tool_output
    (** external tool output *)

    type automaton
    (** internal automaton type *)


    type temp_spec
    type spec_data
    type in_pgrm
    include HardyMisc.Utils.PIPELINE with 
        type in_t = (temp_spec, spec_data, in_pgrm) prog_with_spec and 
        type out_t = (temp_spec, spec_data, in_pgrm) prog_with_spec

    val spec_to_input : Cli.config -> temp_spec list hoare_pair -> tool_input
    
    val exec : Cli.config -> tool_input -> tool_output
    
    val output_to_automaton : Cli.config -> tool_output -> automaton
end

val translate_spec :
  (module S with type automaton = 'automaton and type in_pgrm = 'in_pgrm and type spec_data = 'spec_data and type temp_spec = 'temp_spec) ->
  (module TriplesSig with type automaton = 'automaton and type in_t = 
   ('temp_spec, 'spec_data, 'in_pgrm)
   FrontParser__SharedSyntax.prog_with_spec and type out_t = 'triples) ->
  Cli.config ->
  ('temp_spec, 'spec_data, 'in_pgrm) FrontParser__SharedSyntax.prog_with_spec ->
  'triples
