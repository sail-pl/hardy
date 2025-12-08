module Program = ProgramSyntax
module Fol = FOLSyntax
module Ltl = LTLSyntax
module Shared = SharedSyntax
module Instant = InstantSyntax
module U = HardyMisc.Utils

(* let fol_vars (f : ('a Program.expr, 'ty) Fol.fol) : (string * 'ty) list =
  Fol.fold_fol (fun _ acc -> acc) Program.expr_vars [] f *)

(** {2 type instantiation} *)


type ('ty,'qty) fol_t = ('ty Program.expr, 'qty) Fol.pred_fol

type ('ty, 'qty, 'data) inst_spec_t = (Instant.instant option * 'ty ,'qty) fol_t * 'data
(** instantaneous specification of program expression *)

type ('ty,'qty) temp_spec_t = ('ty,'qty) fol_t Ltl.ltl
(** ltl logic with fol over program expression where variables can be temporally
    quantified *)

type triple_data_t = { triple_id : string }

(** extra information appended to generated hoare triples *)

type parsed_temp_spec_t = (Instant.instant option, Shared.base_ty) temp_spec_t
type parsed_spec_t = (unit,Shared.base_ty) fol_t



type parsed_program =
  (
    parsed_temp_spec_t, 
    parsed_spec_t, 
    unit, 
    Program.parsed_env
  ) Program.program


type base_temp_spec_t = (Instant.instant option * Shared.ty, Shared.base_ty) temp_spec_t
(* Instant.instant should always be None in  base_spec_t, this just allows for uniform processing  *)
type base_spec_t = (Instant.instant option * Shared.ty,Shared.base_ty) fol_t



type base_program =
  (
    base_temp_spec_t, 
    base_spec_t, 
    Shared.ty, 
    Shared.(cat_ty * base_ty) Program.env
  ) Program.program


