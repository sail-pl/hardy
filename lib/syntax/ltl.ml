open Locations
open Operators

(* LTL *)

type ltl_unary =
  | LTL_UArithm of common_logic_unary
  | Next
  | WeakNext
  | Always
  | Eventually

type ltl_binary =
  | LTL_BArithm of common_logic_binary
  | Until
  | WeakUntil
  | Release
  | StrongRelease

type 'a ltl = 'a ltl_ locatable

and 'a ltl_ =
  | LTL_True
  | LTL_False
  | LTL_Pred of 'a
  | LTL_Unary of ltl_unary * 'a ltl
  | LTL_Binary of 'a ltl * ltl_binary * 'a ltl

let ltl_conjunction f1 f2 =
  match (f1, f2) with
  | Some f1, Some f2 ->
      Some (mk_dummy_loc (LTL_Binary (f1, LTL_BArithm And, f2)))
  | Some f, None | None, Some f -> Some f
  | None, None -> None
