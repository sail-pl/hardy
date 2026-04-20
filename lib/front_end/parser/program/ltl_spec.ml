module Program = ProgramSyntax
module Fol = FOLSyntax
module Ltl = LTLSyntax
module Pltl = PLTLSyntax
module Shared = SharedSyntax
module Instant = InstantSyntax
module U = HardyMisc.Utils


(* todo simplify with pltl_spec *)


(* let fol_vars (f : ('a Program.expr, 'ty) Fol.fol) : (string * 'ty) list =
  Fol.fold_fol (fun _ acc -> acc) Program.expr_vars [] f *)

(** {2 type instantiation} *)


type ('ty,'qty) fol_t = ('ty Program.expr, 'qty option) Fol.pred_fol

type ('ty, 'qty, 'data) inst_spec_t = (('ty ,'qty) fol_t, 'data) U.labeled
(** instantaneous specification of program expression *)

type ('atom_label,'ty,'qty) temp_spec_t = ('ty, 'qty, 'atom_label) inst_spec_t Ltl.ltl
(** ltl logic with fol over program expression where variables can be temporally
    quantified *)

(** extra information appended to generated hoare triples *)


type parsed_temp_spec_t = (InstantSyntax.instant option, Shared.base_ty) fol_t Ltl.ltl

type parsed_spec_t = (unit,Shared.base_ty) fol_t


type base_spec_t = (Instant.instant option * Shared.ty,Shared.base_ty) fol_t


(* data of the product automaton transitions *)
type transition_data = {transition_data : Instant.min_nb_instants }

(* type fol_data = {fol_data : unit } *)

(* data of first-order logic formulas *)
type formula_data = {formula_data : Instant.min_nb_instants }

(* data of the conjunction of formulas *)
type cnf_data = {cnf_data : Instant.min_nb_instants}


type triple_data = { triple_id : string ; invariants : base_spec_t list; nb_instants : Instant.min_nb_instants}
