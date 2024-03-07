(** {1 Terms for First Order Logic} *)

open Locations
open Types
open Operators

(** First order Logic formulas parameterized by atomic propositions *)

type 'a fol = 'a fol_ locatable

and 'a fol_ =
  | FOL_True
  | FOL_False
  | Pred of 'a
  | FOL_Unary of common_logic_unary * 'a fol
  | FOL_Binary of 'a fol * common_logic_binary * 'a fol
  | Forall of (string * ty) list * 'a fol
  | Exists of (string * ty) list * 'a fol

(** {1 Helpers to build locatable formulas} *)

let true_fol : 'a fol = mk_dummy_loc FOL_True
let false_fol : 'a fol = mk_dummy_loc FOL_False
let atomic_fol (x : 'a) : 'a fol = mk_dummy_loc (Pred x)
let not_fold (f : 'a fol) : 'a fol = mk_dummy_loc (FOL_Unary (Not, f))

let and_fol (f1 : 'a fol) (f2 : 'a fol) : 'a fol =
  mk_dummy_loc (FOL_Binary (f1, And, f2))

let or_fol (f1 : 'a fol) (f2 : 'a fol) : 'a fol =
  mk_dummy_loc (FOL_Binary (f1, Or, f2))

let xor_fol (f1 : 'a fol) (f2 : 'a fol) : 'a fol =
  mk_dummy_loc (FOL_Binary (f1, Xor, f2))

let equiv_fol (f1 : 'a fol) (f2 : 'a fol) : 'a fol =
  mk_dummy_loc (FOL_Binary (f1, Equiv, f2))

let arrow_fol (f1 : 'a fol) (f2 : 'a fol) : 'a fol =
  mk_dummy_loc (FOL_Binary (f1, Arrow, f2))

let arith_fol b (f1 : 'a fol) (f2 : 'a fol) : 'a fol =
  mk_dummy_loc (FOL_Binary (f1, Arithm b, f2))

let forall_fol (vars : (string * ty) list) (f : 'a fol) : 'a fol =
  mk_dummy_loc (Forall (vars, f))

let exists_fol (vars : (string * ty) list) (f : 'a fol) : 'a fol =
  mk_dummy_loc (Exists (vars, f))
