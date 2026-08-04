open FrontParser
open HardyFrontEnd
open FrontSig
open Specification
open Loopy.Ltl.Spec
(* Typechecks a program with LTL specification *)
module M :  FrontSig.Typing
with type in_t = (Loopy.Ltl.Spec.parsed_temp_spec_t, unit, (Loopy.Ltl.Spec.parsed_spec_t, unit, Loopy.Syntax.parsed_env)  Loopy.Syntax.program) Shared.prog_with_spec
    and type out_t = 
        ((((InstantSyntax.instant option * Shared.ty), Shared.base_ty, temp_f_prop) Loopy.Ltl.Spec.temp_spec_t, temp_f_prop) HardyMisc.Utils.labeled, unit, 
            (base_spec_t, Shared.ty, Shared.ty Loopy.Syntax.env)  Loopy.Syntax.program) Shared.prog_with_spec