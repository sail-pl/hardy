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

module type TriplesSig = sig
  type fol_ty
  type fol_qty
  type fol_data

  type automaton

  val generate_triples : frontend_program -> automaton ->
      ((fol_ty, fol_qty, fol_data) inst_spec_t formula, triple_data_t )
      hoare_triple
      list
end


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

  type in_program = frontend_program
  (* (ty temp_spec_t, (ty,unit) inst_spec_t, variant_t, unit) program *)

  type triples =
    ( (Shared.ty,Shared.base_ty, fol_data) inst_spec_t formula, triple_data)
    hoare_triple
    list

  module Triples : TriplesSig

  val spec_to_input : Cli.info -> base_temp_spec_t list hoare_pair -> input
  val exec : Cli.info -> input -> output
  val output_to_automaton : Cli.info -> output -> automaton
  val generate_triples : in_program -> automaton -> triples
end

let translate_spec (type triple_data fol_data)
    (module M : S
      with type triple_data = triple_data
       and type fol_data = fol_data) info (p : M.in_program) : M.triples =
  M.(
    spec_to_input info p.prog_spec
    |> exec info |> output_to_automaton info |> generate_triples p)
