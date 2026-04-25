open HardyFrontEnd
open FrontSig
open Syntax
open Syntax.Fol
open Syntax.Shared
open Syntax.Instant
open HardyMisc.Utils
open Program

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
    (_ : BuchiSig.S)
    (BProd : BuchiSig.S
        with 
        type E.label = string bool_a BaProduct.arc_data and 
        type vdata = BaProduct.vertex_data)
    (_ : HardyFrontEnd.Cli.CliSig) -> GenSig.TriplesSig with
        type local_spec = T.base_spec_t and
        type temp_spec = ((temp_f_prop, Instant.instant option * ty, base_ty) T.temp_spec_t, temp_f_prop) labeled and
        type automaton = BProd.t  and
        type t = (( ((Instant.instant option * ty, base_ty) T.fol_t, T.formula_data Types.formula_data) labeled cnf, T.cnf_data Types.cnf_data) hoare_triple, T.triple_data Types.triple_data) labeled conjunction
