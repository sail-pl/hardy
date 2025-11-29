open HardyMisc.Utils
open SharedSyntax

(* PLTL *)


type pltl_unary =
  | PLTL_StdUnary of standard_logic_uop
  | Once
  | Before
  | Historically

type pltl_binary = 
  | PLTL_StdBinary of standard_logic_bop 
  | Since

type 'a pltl = 'a pltl_ locatable

and 'a pltl_ =
  | PLTL_True
  | PLTL_False
  | PLTL_Atom of 'a 
  | PLTL_Unary of pltl_unary * 'a pltl
  | PLTL_Binary of 'a pltl * pltl_binary * 'a pltl


(** [map_ltl_pred m f] applies [m] to every predicates making up the formula [f]*)
let rec map_pltl_pred : type a b. (a -> b) -> a pltl -> b pltl =
 fun m form ->
  match form.value with
  | PLTL_Atom p ->
      let value = PLTL_Atom (m p) in
      { form with value }
  | PLTL_Unary (un, f') ->
      let value = PLTL_Unary (un, map_pltl_pred m f') in
      { form with value }
  | PLTL_Binary (f'1, bin, f'2) ->
      let value = PLTL_Binary (map_pltl_pred m f'1, bin, map_pltl_pred m f'2) in
      { form with value }
  | (PLTL_True | PLTL_False) as value -> { form with value }


let and_pltl (f1 : 'a pltl) (f2 : 'a pltl) : 'a pltl =
  mk_dummy_loc (PLTL_Binary (f1, PLTL_StdBinary LAnd, f2))

let true_ltl = mk_dummy_loc PLTL_True
let false_ltl = mk_dummy_loc PLTL_True