open HardyFrontEnd
open Syntax
open Program

(** [M(TempSpec)(BaseSpec)(TriplesT)]*)
module M :
  (BaseSpec : HardyMisc.Utils.SIMP_TYPE)(TempSpec : HardyMisc.Utils.SIMP_TYPE) (TriplesType : HardyMisc.Utils.SIMP_TYPE)
   ->
     Sig.S with 
    type program = (TempSpec.t, unit, BaseSpec.t, Shared.ty, Shared.ty env) Syntax.Program.program * Why3.Ptree.mlw_file and 
    type triples = TriplesType.t

