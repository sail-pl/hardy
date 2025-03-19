module Program = ProgramSyntax
module Fol = FOLSyntax
module Ltl = LTLSyntax
module Shared = SharedSyntax

(** {2 type instantiation} *)

type 'ty inst_spec_t = (Program.expr, 'ty) Fol.fol
(** instantaneous specification of program expression *)

type 'ty temp_spec_t = 'ty inst_spec_t Ltl.ltl
(** ltl logic with fol over program expression *)

type variant_t = Program.(expr variant)
(** variant expression: only allowed to be a program expression *)

type fun_id_t = string Program.fun_id

type base_program =
  (Shared.ty temp_spec_t, Shared.ty inst_spec_t, variant_t) Program.program
