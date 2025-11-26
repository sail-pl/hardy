(** {1 Middle-end signature}*)

module Cli = HardyFrontEnd.Cli
open HardyFrontEnd.Syntax.Program
open FrontParser.Program
open HardyMisc.Utils


(* Tool for generating the automata *)
module type ToolSig = sig
  type input
  type output

  val call : Cli.info -> (string -> string) ->  input -> output
  
end

(* triples are in cnf *)
type 'f formula = 'f cnf

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

  type triple_data
  (** additional information over a triple *)

  type fol_data
  (** additional information over a formula *)

  type in_program = base_program
  (* (ty temp_spec_t, (ty,unit) inst_spec_t, variant_t, unit) program *)

  type triples =
    ( triple_data,
      (Shared.ty, fol_data) inst_spec_t formula )
    hoare_triple
    list

  val spec_to_input : Cli.info -> Shared.ty temp_spec_t list hoare_pair -> input
  val exec : Cli.info -> input -> output
  val output_to_automaton : Cli.info -> output -> automaton
  val generate_triples : in_program -> automaton -> triples
end

let translate_spec (type triple_data) (type fol_data)
    (module M : S
      with type triple_data = triple_data
       and type fol_data = fol_data) info (p : M.in_program) : M.triples =
  M.(
    spec_to_input info p.prog_spec
    |> exec info |> output_to_automaton info |> generate_triples p)
