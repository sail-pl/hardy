(** {1 Terms for First Order Logic} *)

open HardyMisc.Utils
open SharedSyntax

type ('a, 'qty) fol = ('a, 'qty) fol_ locatable
(** First order Logic formulas parameterized by atomic propositions *)

and ('a, 'qty) fol_ =
  | FOL_True
  | FOL_False
  | Pred of 'a
  | FOL_Unary of common_logic_unary * ('a, 'qty) fol
  | FOL_Binary of ('a, 'qty) fol * common_logic_binary * ('a, 'qty) fol
  | Forall of (string * 'qty) list * ('a, 'qty) fol
  | Exists of (string * 'qty) list * ('a, 'qty) fol
  | ExistsPrev of
      string * ('a, 'qty) fol (* temporal existential quantification *)

let map_fol : type a b ty_a ty_b.
    ((a, ty_a) fol -> (b, ty_b) fol) ->
    (string * ty_a -> string * ty_b) ->
    (a, ty_a) fol ->
    (b, ty_b) fol =
 fun m m_ty form ->
  match form.value with
  | FOL_True | FOL_False | Pred _ -> m form
  | FOL_Unary (o, f) ->
      let value = FOL_Unary (o, m f) in
      { form with value }
  | FOL_Binary (f1, o, f2) ->
      let value = FOL_Binary (m f1, o, m f2) in
      { form with value }
  | Forall (l, f) ->
      let value = Forall (List.map m_ty l, m f) in
      { form with value }
  | Exists (l, f) ->
      let value = Exists (List.map m_ty l, m f) in
      { form with value }
  | ExistsPrev (v, f) ->
      let value = ExistsPrev (v, m f) in
      { form with value }

let rec fold_fol : type a b t.
    ((a, t) fol -> b -> b) -> (a -> b -> b) -> b -> (a, t) fol -> b =
 fun j pj init form ->
  match form.value with
  | FOL_True | FOL_False -> j form init
  | Pred p -> pj p init
  | FOL_Unary (_, f) -> j form (fold_fol j pj init f)
  | FOL_Binary (f1, _, f2) -> j form (fold_fol j pj (fold_fol j pj init f1) f2)
  | Forall (_, f) | Exists (_, f) | ExistsPrev (_, f) ->
      j form (fold_fol j pj init f)

(** [map_fol_ty m f] replaces every quantifer [Exists (l,e)] and [Forall (l,e)]
    of [f] by [X (List.map m l,e)] *)
let rec map_fol_ty m = map_fol (map_fol_ty m) m

(** [map_fol_pred m f] replaces every predicate [Pred x] of [f] by [Pred (m x)]
*)
let rec map_fol_pred m =
  map_fol
    (function
      | { value = Pred x; label = loc } -> { value = Pred (m x); label = loc }
      | e -> map_fol_pred m e)
    Fun.id

(** {2 Helpers to build locatable formulas} *)

let true_fol : ('a, 'b) fol = mk_dummy_loc FOL_True
let false_fol : ('a, 'b) fol = mk_dummy_loc FOL_False
let atomic_fol (x : 'a) : ('a, 'b) fol = mk_dummy_loc (Pred x)

let not_fold (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_Unary (Not, f))

let and_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_Binary (f1, Arithm And, f2))

let or_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_Binary (f1, Arithm Or, f2))

let equiv_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_Binary (f1, Equiv, f2))

let arrow_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_Binary (f1, Arrow, f2))

let arith_fol b (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_Binary (f1, Arithm b, f2))

let forall_fol (vars : (string * 'qty) list) (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (Forall (vars, f))

let exists_fol (vars : (string * 'qty) list) (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (Exists (vars, f))
