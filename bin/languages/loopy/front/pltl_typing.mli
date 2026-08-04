open FrontParser
open Loopy.Ppltl.Spec
open HardyFrontEnd
open FrontSig
(* Typechecks a program with pure-past LTL specification *)
module M 

: FrontSig.Typing with
    type in_t =  (parsed_temp_spec_t, unit, 
        (parsed_spec_t, unit, Loopy.Syntax.parsed_env)  Loopy.Syntax.program) Shared.prog_with_spec and
    type out_t = ( (((Specification.InstantSyntax.instant option * Shared.ty), Shared.base_ty, temp_f_prop) temp_spec_t, temp_f_prop) U.labeled, unit,
        (base_spec_t, Shared.ty, Shared.ty Loopy.Syntax.env)  Loopy.Syntax.program) Syntax.Shared.prog_with_spec
     