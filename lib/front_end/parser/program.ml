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

type ('ty, 'qty, 'data) inst_spec_t = ((Instant.instant option * 'ty ,'qty) fol_t, 'data) U.labeled
(** instantaneous specification of program expression *)

type ('atom_label,'ty,'qty) temp_spec_t = (('ty,'qty) fol_t, 'atom_label) U.labeled Ltl.ltl
(** ltl logic with fol over program expression where variables can be temporally
    quantified *)

(** extra information appended to generated hoare triples *)

type parsed_temp_spec_t = (unit, Instant.instant option, Shared.base_ty) temp_spec_t
type parsed_spec_t = (unit,Shared.base_ty) fol_t

type temp_f_prop = {
    mentions_input: bool;
    mentions_output: bool;
    mentions_state: bool;
}

let is_static_prop p = not (p.mentions_input || p.mentions_output || p.mentions_state)

let dft_temp_f_prop = {mentions_input=false; mentions_output=false; mentions_state=false} 

let join_temp_f_prop p1 p2 = 
  let mentions_input = p1.mentions_input || p2.mentions_input 
  and mentions_output = p1.mentions_output || p2.mentions_output
  and mentions_state = p1.mentions_state || p2.mentions_state
  in
  {mentions_input ; mentions_output; mentions_state}



type base_temp_spec_t = ((temp_f_prop, Instant.instant option * Shared.ty, Shared.base_ty) temp_spec_t, temp_f_prop) U.labeled
(* Instant.instant should always be None in  base_spec_t, this just allows for uniform processing  *)
type base_spec_t = (Instant.instant option * Shared.ty,Shared.base_ty) fol_t

type triple_data_t = { triple_id : string ; invariants : base_spec_t list; min_nb_instants: Instant.min_nb_instants option}


type parsed_program =
  (
    parsed_temp_spec_t, 
    unit,
    parsed_spec_t, 
    unit, 
    Program.parsed_env
  ) Program.program

type frontend_program =
  (
    base_temp_spec_t, 
    unit,
    base_spec_t, 
    Shared.ty, 
    Shared.(cat_ty * base_ty) Program.env
  ) Program.program

type middleend_program =
  (
    base_temp_spec_t, 
    unit,
    base_spec_t, 
    Shared.ty, 
    Shared.(cat_ty * base_ty) Program.env
  ) Program.program

  type backend_program =
  (
    base_temp_spec_t, 
    unit,
    base_spec_t, 
    Shared.ty, 
    Shared.(cat_ty * base_ty) Program.env
  ) Program.program


