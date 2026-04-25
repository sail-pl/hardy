open FrontParser
open Ltl_spec
open FrontSig

(* Typechecks a program with LTL specification *)
module M : FrontSig.Typing with
    type in_local_spec = parsed_spec_t and
    type in_temp_spec = parsed_temp_spec_t and
    type out_temp_spec = ((temp_f_prop, (InstantSyntax.instant option * Shared.ty), Shared.base_ty) temp_spec_t, temp_f_prop) U.labeled and
    type out_local_spec = base_spec_t
