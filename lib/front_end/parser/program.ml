module Program = ProgramSyntax
module Fol = FOLSyntax
module Ltl = LTLSyntax
module Shared = SharedSyntax
module Instant = InstantSyntax
module U = HardyMisc.Utils

(* let fol_vars (f : ('a Program.expr, 'ty) Fol.fol) : (string * 'ty) list =
  Fol.fold_fol (fun _ acc -> acc) Program.expr_vars [] f *)

(** {2 type instantiation} *)

type 'ty fol_t = (Instant.instant option Program.expr, 'ty) Fol.pred_fol

type ('ty, 'data) inst_spec_t = 'ty fol_t U.cnf * 'data
(** instantaneous specification of program expression *)

type 'ty temp_spec_t = 'ty fol_t Ltl.ltl
(** ltl logic with fol over program expression where variables can be temporally
    quantified *)

type triple_data_t = { triple_id : string }

(** extra information appended to generated hoare triples *)

type parsed_program =
  (Shared.ty temp_spec_t, Shared.ty fol_t, unit, Program.parsed_env) Program.program


type base_program =
  (Shared.ty temp_spec_t, Shared.ty fol_t, unit, Shared.(cat_ty * base_ty) Program.env) Program.program


