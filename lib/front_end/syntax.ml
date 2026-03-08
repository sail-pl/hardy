include FrontParser

module Program = FrontParser.ProgramSyntax
module Fol = FOLSyntax
module Ltl = LTLSyntax
module Pltl = PLTLSyntax
module Shared = SharedSyntax
module Instant = InstantSyntax
module U = HardyMisc.Utils


(* include FrontParser.Program *)

(* module type SpecTypes = sig 
  type eba_data
  type fol_data
  type formula_data
  type cnf_data
  type triple_data
end


module LtlSpec  = struct
  type eba_data = {eba_data : Instant.min_nb_instants }
  type fol_data = {fol_data : Instant.min_nb_instants }
  type formula_data = {formula_data : Instant.min_nb_instants }
  type cnf_data = {cnf_data : Instant.min_nb_instants}
  type triple_data = { triple_id : string ; invariants : base_spec_t list; nb_instants : Instant.min_nb_instants}
end *)