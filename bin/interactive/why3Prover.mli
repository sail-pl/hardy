open HardyFrontEnd
open Syntax

(** [M(ProgramType)(TriplesT)]*)
module M :
  (ProgramType: HardyMisc.Utils.SIMP_TYPE) 
  (TriplesType : HardyMisc.Utils.SIMP_TYPE)
   ->
     Sig.S with 
    type program = ProgramType.t * Why3.Ptree.mlw_file and 
    type triples = TriplesType.t

