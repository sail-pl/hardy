open FrontParser
open SharedSyntax
open HardyFrontEnd
open FrontSig
open HardyMisc.Utils
open Specification

(*** Specification atoms are FOL formulas *)
module AtomicFormula :
sig
    type t = (
        (InstantSyntax.instant option * ty, base_ty) Loopy.Ltl.Spec.fol_t, 
        temp_f_prop
    ) labeled
end

module Parsing : HardyFrontEnd.Parsing.S with type out_t = (Loopy.Ltl.Spec.parsed_temp_spec_t, unit, (Loopy.Ltl.Spec.parsed_spec_t, unit, FrontParser.Loopy.Syntax.parsed_env) FrontParser.Loopy.Syntax.program) prog_with_spec


module Typing = Ltl_typing.M

(** automaton type *)
module B : sig type t end

(** product automaton type *)
module BProd : sig type t end 

(** Middle end processes LTL specification where atoms are of type [AtomicFormula.t]*)
module Middle : HardyMiddleEnd.MidSig.S with
    type temp_spec = (AtomicFormula.t LTLSyntax.ltl, temp_f_prop) labeled and
    type spec_data = unit and
    type automaton = BProd.t and
    type in_pgrm = (Loopy.Ltl.Spec.base_spec_t, ty, ty Loopy.Syntax.env) Loopy.Syntax.program

(** Triples are a conjunction of hoare-style FOL formulas *)
module Triples : 
    (_ : HardyFrontEnd.Cli.CliSig) -> HardyMiddleEnd.Automata.GenSig.TriplesSig with
    type automaton = BProd.t and
    type in_t = (Middle.temp_spec, Middle.spec_data, Middle.in_pgrm) prog_with_spec and 
    type out_t = (
        (
            (
                (InstantSyntax.instant option *  ty, base_ty) Loopy.Ltl.Spec.fol_t,
                Loopy.Ltl.Spec.formula_data Types.formula_data
            ) labeled cnf,
            
            Loopy.Ltl.Spec.cnf_data Types.cnf_data
        )
        hoare_triple,
        Loopy.Ltl.Spec.triple_data Types.triple_data
    ) labeled conjunction

module Interactive : (_ : HardyFrontEnd.Cli.CliSig) -> Interactive.Sig.S with
    type program = Middle.in_t * Why3.Ptree.mlw_file  and
    type triples = (((
        (InstantSyntax.instant option * ty, base_ty) Loopy.Ltl.Spec.fol_t, 
        Loopy.Ltl.Spec.formula_data Types.formula_data
    ) labeled cnf, Loopy.Ltl.Spec.cnf_data Types.cnf_data) hoare_triple, Loopy.Ltl.Spec.triple_data Types.triple_data) labeled conjunction


module Back : (_ : HardyFrontEnd.Cli.CliSig) -> HardyBackEnd.BackSig.S with 
    type in_fun = Loopy.Ltl.Spec.cnf_data Types.cnf_data and
    type in_spec = (
        (InstantSyntax.instant option * ty, base_ty) Loopy.Ltl.Spec.fol_t, 
        Loopy.Ltl.Spec.formula_data Types.formula_data
    ) labeled cnf and
    (* type local_spec = Middle.local_spec and *)
    type temp_spec = Middle.temp_spec and
    type in_t = (((InstantSyntax.instant option * ty, base_ty, temp_f_prop) Loopy.Ltl.Spec.temp_spec_t, temp_f_prop)  labeled, unit, (Loopy.Ltl.Spec.base_spec_t, ty, ty Loopy.Syntax.env) Loopy.Syntax.program) prog_with_spec and
    type out_t = Why3.Ptree.mlw_file and
    type triple_data = Loopy.Ltl.Spec.triple_data Types.triple_data
