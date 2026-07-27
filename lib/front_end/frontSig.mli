open Syntax.SharedSyntax

(** provides information about what category of identifier is mentionned inside a temporal formula *)
type temp_f_prop = {
    mentions_input : bool;
    mentions_output : bool;
    mentions_state : bool;
    mentions_history : bool;
}

val mentions_temp_f_prop : cat_ty -> temp_f_prop

val is_static_prop : temp_f_prop -> bool

val dft_temp_f_prop : temp_f_prop

val join_temp_f_prop : temp_f_prop -> temp_f_prop -> temp_f_prop

(** Signature for program typechecking *)
module type Typing =
sig
    include HardyMisc.Utils.PIPELINE

    type out_local_spec 
    val type_pgrm : in_t -> out_t
end
