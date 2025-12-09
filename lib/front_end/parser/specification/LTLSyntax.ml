open HardyMisc.Utils
open SharedSyntax
open PLTLSyntax

(** 1-level Linear Temporal Logic formulas nested with Pure-past LTL parameterized by predicates *)

type ltl_unary =
  | Next
  | Always
  | Eventually

type ltl_binary =
  | Until
  | WeakUntil
  | Release
  | StrongRelease

(** 1-level Linear Temporal Logic formulas nested with Pure-past LTL parameterized by predicates *)
type 'a ltl = 'a ltl_ locatable

and 'a ltl_ =
  | LTL_True
  | LTL_False
  | LTL_Atom of 'a pltl
  | LTL_StdUnary of standard_logic_uop * 'a ltl
  | LTL_Unary of ltl_unary * 'a pltl
  | LTL_StdBinary of 'a ltl * standard_logic_bop * 'a ltl
  | LTL_Binary of 'a pltl * ltl_binary * 'a pltl


(** [map_ltl_pred m f] applies [m] to every predicates making up the formula [f]*)
let rec map_ltl_pred : type a b. (a -> b) -> a ltl -> b ltl =
 fun m form ->
  match form.value with
  | LTL_Atom p ->
      let value = LTL_Atom (map_pltl_pred m p) in
      { form with value }
  | LTL_StdUnary (un, f') ->
    let value = LTL_StdUnary (un, map_ltl_pred m f') in
    { form with value }
  | LTL_Unary (un, f') ->
      let value = LTL_Unary (un, map_pltl_pred m f') in
      { form with value }
  | LTL_StdBinary  (f'1, bin, f'2) -> 
     let value = LTL_StdBinary (map_ltl_pred m f'1, bin, map_ltl_pred m f'2) in
      { form with value }
  | LTL_Binary (f'1, bin, f'2) ->
      let value = LTL_Binary (map_pltl_pred m f'1, bin, map_pltl_pred m f'2) in
      { form with value }
  | (LTL_True | LTL_False) as value -> { form with value }

(** {2 Helpers to build locatable formulas} *)

let and_ltl (f1 : 'a ltl) (f2 : 'a ltl) : 'a ltl =
  mk_dummy_loc (LTL_StdBinary (f1, LAnd, f2))

let true_ltl = mk_dummy_loc LTL_True
let false_ltl = mk_dummy_loc LTL_True