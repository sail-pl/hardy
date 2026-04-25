open Format
open FrontParser
open ProgramSyntax
open SharedSyntax

(** {1 Pretty-printing of program types, expressions and specifications} *)

val pp_cat_ty : formatter -> cat_ty -> unit

val pp_base_ty : formatter -> base_ty -> unit

val pp_ty : formatter -> cat_ty * base_ty -> unit

val pp_unop : formatter -> standard_logic_uop -> unit

val pp_expr_binop : formatter -> expr_binop -> unit

val pp_common_logic_binary : formatter -> standard_logic_bop -> unit

val pp_hist :
  formatter ->
  string * InstantSyntax.instant option -> unit

val pp_paren_exp :
  (formatter ->
   ('a expression_, 'b) HardyMisc.Utils.labeled ->
   unit) ->
  formatter ->
  ('a expression_, 'b) HardyMisc.Utils.labeled ->
  unit

  val pp_exp :
  (formatter -> string * 't -> unit) ->
  formatter ->
  ('t expression_, HardyMisc.Utils.loc option)
  HardyMisc.Utils.labeled -> unit

val pp_paren_fol :
  (formatter -> ('a, 'b) FOLSyntax.fol -> unit) ->
  (formatter -> 'a -> unit) ->
  formatter -> ('a, 'b) FOLSyntax.fol -> unit

val pp_fol :
  (formatter -> 'a -> unit) ->
  (formatter -> 'b -> unit) ->
  formatter -> ('a, 'b) FOLSyntax.fol -> unit

val pp_pred :
  (formatter -> 'a -> unit) ->
  formatter -> 'a FOLSyntax.predicate -> unit

val pp_ltl_binop :
  formatter -> LTLSyntax.ltl_binary -> unit

val pp_ltl_unop : formatter -> LTLSyntax.ltl_unary -> unit

val pp_ltl_binop_spin :
  formatter -> LTLSyntax.ltl_binary -> unit

val pp_ltl_unnop_spin :
  formatter -> LTLSyntax.ltl_unary -> unit

val pp_ltl :
  (formatter -> 'a -> unit) ->
  (formatter -> LTLSyntax.ltl_binary -> unit) ->
  (formatter -> LTLSyntax.ltl_unary -> unit) ->
  formatter -> 'a LTLSyntax.ltl -> unit

val pp_pltl_binop :
  formatter -> PpLTLSyntax.pltl_binary -> unit

val pp_pltl_unop :
  formatter -> PpLTLSyntax.pltl_unary -> unit

val pp_ltl_default :
  (formatter -> 'a -> unit) ->
  formatter -> 'a LTLSyntax.ltl -> unit

val pp_pltl :
  (formatter -> 'a -> unit) ->
  (formatter -> PpLTLSyntax.pltl_binary -> unit) ->
  (formatter -> PpLTLSyntax.pltl_unary -> unit) ->
  formatter -> 'a PpLTLSyntax.pltl -> unit

val pp_pltl_default :
  (formatter -> 'a -> unit) ->
  formatter -> 'a PpLTLSyntax.pltl -> unit
