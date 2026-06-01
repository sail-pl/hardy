open FrontParser
open SharedSyntax
open ProgramSyntax
open HardyFrontEnd.FrontSig
open HardyMisc.Utils

(* Specification atoms are FOL formulas *)
module AtomicFormula :
sig
    type t = (
        (InstantSyntax.instant option * ty, base_ty) Ppltl_spec.fol_t, 
        temp_f_prop
    ) labeled
end

module Parsing : HardyFrontEnd.Parsing.S with 
    type local_spec = Ppltl_spec.parsed_spec_t and
    type temp_spec = Ppltl_spec.parsed_temp_spec_t


module Typing = HardyFrontEnd.Pltl_typing.M

(** automaton type *)
module B : sig type t end

(** product automaton type *)
module BProd : sig type t end 

(** Middle end processes Pure-past LTL specification where atoms are of type [AtomicFormula.t]*)
module Middle : HardyMiddleEnd.MidSig.S with
    type local_spec = Typing.out_local_spec and
    type temp_spec = (AtomicFormula.t PpLTLSyntax.pltl LTLSyntax.ltl, temp_f_prop) labeled and
    type automaton = BProd.t

(** Triples are a conjunction of hoare-style FOL formulas *)
module Triples : 
    (_ : HardyFrontEnd.Cli.CliSig) -> HardyMiddleEnd.Automata.GenSig.TriplesSig with
    type automaton = BProd.t and
    type t = (
        (
            (
                (InstantSyntax.instant option *  ty, base_ty) Ppltl_spec.fol_t,
                Ppltl_spec.formula_data Types.formula_data
            ) labeled cnf,
            
            Ppltl_spec.cnf_data Types.cnf_data
        )
        hoare_triple,
        Ppltl_spec.triple_data Types.triple_data
    ) labeled conjunction and
    type local_spec = Typing.out_local_spec and

    type temp_spec = (
        (temp_f_prop, InstantSyntax.instant option * ty, base_ty) Ppltl_spec.temp_spec_t,
        temp_f_prop
        ) labeled 


module Interactive : (_ : HardyFrontEnd.Cli.CliSig) -> Sig.S with
    type program = Middle.in_program * Why3.Ptree.mlw_file  and
    type triples = (((
        (InstantSyntax.instant option * ty, base_ty) Ppltl_spec.fol_t, 
        Ppltl_spec.formula_data Types.formula_data
    ) labeled cnf, Ppltl_spec.cnf_data Types.cnf_data) HardyFrontEnd.Syntax.Program.hoare_triple, Ppltl_spec.triple_data Types.triple_data) labeled conjunction


module Back : (_ : HardyFrontEnd.Cli.CliSig) -> HardyBackEnd.BackSig.S with 
    type in_fun = Ppltl_spec.cnf_data Types.cnf_data and
    type in_spec = (
        (InstantSyntax.instant option * ty, base_ty) Ppltl_spec.fol_t, 
        Ppltl_spec.formula_data Types.formula_data
    ) labeled cnf and
    type local_spec = Middle.local_spec and
    type temp_spec = Middle.temp_spec and
    type out_pgrm = Why3.Ptree.mlw_file and
    type triple_data = Ppltl_spec.triple_data Types.triple_data
