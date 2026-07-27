open FrontParser
open Ltl_spec
open HardyFrontEnd
open FrontSig

(* Typechecks a program with LTL specification *)
module M :  FrontSig.Typing
with type in_t = (parsed_temp_spec_t, unit, (parsed_spec_t, unit, Syntax.LoopySyntax.parsed_env)  Syntax.LoopySyntax.program) Shared.prog_with_spec
    and type out_t = 
        ((((InstantSyntax.instant option * Shared.ty), Shared.base_ty, temp_f_prop) temp_spec_t, temp_f_prop) U.labeled, unit, 
            (base_spec_t, Shared.ty, Shared.ty Syntax.LoopySyntax.env)  Syntax.LoopySyntax.program) Shared.prog_with_spec