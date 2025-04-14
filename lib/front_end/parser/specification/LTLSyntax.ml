(** {1 Terms for (Propositional) Linear Temporal Logic} *)

open HardyMisc.Utils
open SharedSyntax

(* LTL *)

type ltl_unary =
  | LTL_UArithm of common_logic_unary
  | Next
  | Always
  | Eventually

type ltl_binary =
  | LTL_BArithm of common_logic_binary
  | Until
  | WeakUntil
  | Release
  | StrongRelease

(** Linear Temporal Logic formulas parameterized by predicates *)

type 'a ltl = 'a ltl_ locatable

and 'a ltl_ =
  | LTL_True
  | LTL_False
  | LTL_Pred of 'a
  | LTL_Unary of ltl_unary * 'a ltl
  | LTL_Binary of 'a ltl * ltl_binary * 'a ltl

(** [map_ltl_pred m f] applies [m] to every predicates making up the formula [f]*)
let rec map_ltl_pred : type a b. (a -> b) -> a ltl -> b ltl =
 fun m form ->
  match form.value with
  | LTL_Pred p ->
      let value = LTL_Pred (m p) in
      { form with value }
  | LTL_Unary (un, f') ->
      let value = LTL_Unary (un, map_ltl_pred m f') in
      { form with value }
  | LTL_Binary (f'1, bin, f'2) ->
      let value = LTL_Binary (map_ltl_pred m f'1, bin, map_ltl_pred m f'2) in
      { form with value }
  | (LTL_True | LTL_False) as value -> { form with value }

(** {2 Helpers to build locatable formulas} *)

let and_ltl (f1 : 'a ltl) (f2 : 'a ltl) : 'a ltl =
  mk_dummy_loc (LTL_Binary (f1, LTL_BArithm (Arithm And), f2))

let true_ltl = mk_dummy_loc LTL_True
let false_ltl = mk_dummy_loc LTL_True
