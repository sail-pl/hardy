(** {1 Middle-end signature}*)

open FrontParser.SharedSyntax
open FrontParser.ProgramSyntax

module Cli = HardyFrontEnd.Cli

module type TriplesSig =
sig
    type automaton
    (** input *)

    type t
    (** output *)

    type local_spec
    type temp_spec
    val generate_triples :
      (temp_spec, 'a, local_spec, 'b, 'c) program ->
      automaton -> t
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

    type temp_spec
    type local_spec

    type automaton
    (** internal automaton type *)


    type in_program = (temp_spec, unit, local_spec, ty, ty env) program
    
    val spec_to_input : Cli.config -> temp_spec list hoare_pair -> tool_input
    
    val exec : Cli.config -> tool_input -> tool_output
    
    val output_to_automaton : Cli.config -> tool_output -> automaton
end

val translate_spec :
    (module S with type automaton = 'automaton and type local_spec = 'local_spec and type temp_spec = 'temp_spec) ->
    (module TriplesSig with type automaton = 'automaton and type local_spec = 'local_spec and type t = 'triples and type temp_spec = 'temp_spec) ->
    Cli.config ->
    ('temp_spec, unit, 'local_spec, ty,
    ty env)
    program -> 'triples
