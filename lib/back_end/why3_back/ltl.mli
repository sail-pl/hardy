open HardyFrontEnd
open Syntax
open Instant
open Shared
open HardyMisc.Utils

module M :
  (T: Types.T with 
    type ('ty,'qty) fol_t = ('ty Program.expr, 'qty option) Fol.pred_fol and
    type base_spec_t = ((instant option * Shared.ty) Program.expr, Shared.base_ty option) Fol.pred_fol and
    type triple_data = (triple_id : string * invariants : ((instant option * Shared.ty) Program.expr, Shared.base_ty option) Fol.pred_fol list * nb_instants : Instant.min_nb_instants) and
    type formula_data = min_nb_instants
  )
    -> BackSig.S with 
        type local_spec = ((instant option * Shared.ty) Program.expr, Shared.base_ty option) Fol.pred_fol and
        type temp_spec = ((FrontSig.temp_f_prop, instant option * ty, base_ty) T.temp_spec_t, FrontSig.temp_f_prop) labeled and
        type in_fun = T.cnf_data Types.cnf_data and
        type in_spec = ((instant option * Shared.ty, Shared.base_ty) T.fol_t, T.formula_data Types.formula_data) labeled cnf and
        type triple_data = T.triple_data Types.triple_data  and
        type out_pgrm = Why3.Ptree.mlw_file 