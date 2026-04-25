open Syntax.ProgramSyntax
open Syntax.SharedSyntax

(** provides information about what category of identifier is mentionned inside a temporal formula *)
type temp_f_prop = {
    mentions_input : bool;
    mentions_output : bool;
    mentions_state : bool;
    mentions_history : bool;
}

val is_static_prop : temp_f_prop -> bool

val dft_temp_f_prop : temp_f_prop

val join_temp_f_prop : temp_f_prop -> temp_f_prop -> temp_f_prop

(** Signature for program typechecking *)
module type Typing =
sig
    type in_local_spec
    type in_temp_spec
    type out_local_spec
    type out_temp_spec

    val type_pgrm :
        (in_temp_spec, unit, in_local_spec, unit, parsed_env) program ->
        (out_temp_spec, unit, out_local_spec, ty, ty env) program
end
