open HardyFrontEnd
open FrontSig
open HardyMiddleEnd
open Syntax
open Syntax.Fol
open Syntax.Shared
open Syntax.Instant
open HardyMisc.Utils

(** Construction of triples from the automata *)
module M :
    (T :  Types.T with 
        type transition_data = min_nb_instants and 
        type formula_data = min_nb_instants and
        type cnf_data = min_nb_instants and
        type base_spec_t = ((instant option * ty) expr, base_ty option) pred_fol and
        type triple_data = (triple_id : string * invariants : ((instant option * ty) expr, base_ty option) pred_fol list * nb_instants : Instant.min_nb_instants) and
        type ('ty,'qty) fol_t = ('ty expr, 'qty option) pred_fol
    )
    (_ : Atom.S with 
        type 'a t = 'a (* imperative version for simplicity *) and  
        type atom = ((Instant.instant option * ty, base_ty) T.fol_t, temp_f_prop) labeled)
    (_ : Automata.Buchi.BuchiSig.S)
    (BProd : Automata.Buchi.BuchiSig.S
        with 
        type E.label = string bool_a Automata.Buchi.BaProduct.arc_data and 
        type vdata = Automata.Buchi.BaProduct.vertex_data)
    (_ : HardyFrontEnd.Cli.CliSig) -> 
    Automata.GenSig.TriplesSig with
        type automaton = BProd.t  and
        type in_t = ( 
                            (
                                (Instant.instant option * ty, base_ty, temp_f_prop) T.temp_spec_t, 
                                temp_f_prop
                            ) labeled, 
                        unit,
                        (T.base_spec_t, Shared.ty, Shared.ty Syntax.LoopySyntax.env)  Syntax.LoopySyntax.program
                    ) prog_with_spec and
        type out_t = (
                        ( 
                                (
                                    (Instant.instant option * ty, base_ty) T.fol_t, 
                                    T.formula_data Types.formula_data                                    
                                ) labeled cnf, 
                                T.cnf_data Types.cnf_data
                        ) hoare_triple, 
                        T.triple_data Types.triple_data
                    ) labeled conjunction
