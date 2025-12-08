(** {1 Terms for First Order Logic} *)

open HardyMisc.Utils
open SharedSyntax

type ('a, 'qty) fol = ('a, 'qty) fol_ locatable
(** First order Logic formulas parameterized by atomic propositions *)

and ('a, 'qty) fol_ =
  | FOL_True
  | FOL_False
  | FOL_Atom of 'a
  | FOL_StdUnary of standard_logic_uop * ('a, 'qty) fol
  | FOL_StdBinary of ('a, 'qty) fol * standard_logic_bop * ('a, 'qty) fol
  
  (* convention: 
    LAnd [] <=> LOr []  <=> True 
  *)
  | FOL_StdNary of standard_logic_bop * ('a, 'qty) fol list
  
  
  | Forall of (string * 'qty) list * ('a, 'qty) fol
  | Exists of (string * 'qty) list * ('a, 'qty) fol
  | ExistsPrev of
      string * ('a, 'qty) fol (* temporal existential quantification *)


type 'a predicate = Atom of 'a | Predicate of {name: string; args: 'a list}

type ('a, 'qty) pred_fol = ('a predicate, 'qty) fol

type 'qty pred_decl = {name: string; params: string list; body: (string,'qty) fol }

let map_fol : type a b ty_a ty_b.
    ((a, ty_a) fol -> (b, ty_b) fol) ->
    (string * ty_a -> string * ty_b) ->
    (a, ty_a) fol ->
    (b, ty_b) fol =
 fun m m_ty form ->
  match form.value with
  | FOL_True | FOL_False | FOL_Atom _ -> m form
  | FOL_StdUnary (o, f) ->
      let value = FOL_StdUnary (o, m f) in
      { form with value }
  | FOL_StdBinary (f1, o, f2) ->
      let value = FOL_StdBinary (m f1, o, m f2) in
      { form with value }
  | FOL_StdNary (o,l) ->
      let value = FOL_StdNary (o, List.map m l) in
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
    (b -> (a, t) fol  -> b) -> (b -> a -> b) -> b -> (a, t) fol -> b =
 fun j pj init form ->
  match form.value with
  | FOL_True | FOL_False -> j init form 
  | FOL_Atom p -> pj init p 
  | FOL_StdUnary (_, f) -> j (fold_fol j pj init f) form
  | FOL_StdBinary (f1, _, f2) -> j (fold_fol j pj (fold_fol j pj init f1) f2) form
  | FOL_StdNary (_,l) -> j (List.fold_left (fold_fol j pj) init l) form
  | Forall (_, f) | Exists (_, f) | ExistsPrev (_,f) -> j (fold_fol j pj init f) form

(** [map_fol_ty m f] replaces every quantifer [Exists (l,e)] and [Forall (l,e)]
    of [f] by [X (List.map m l,e)] *)
let rec map_fol_ty m = map_fol (map_fol_ty m) m

(** [map_fol_pred m f] replaces every atom [x] of [f] by [m x]
*)
let map_fol_pred_ty (type a b ty_a ty_b) 
  (fty : ty_a -> ty_b)  (m : a -> b) (f: (a predicate, ty_a) fol) : (b predicate, ty_b) fol =
  let rec map : (a predicate, ty_a) fol -> (b predicate, ty_b) fol = fun f -> match f.value with
      | FOL_Atom Atom x -> 
          {f with value = FOL_Atom (Atom (m x))}
      | FOL_Atom Predicate x -> 
          let args = List.map m x.args in
          {f with value = FOL_Atom (Predicate {x with args})}
      | FOL_True | FOL_False as f -> mk_dummy_loc f
      | _ -> map_fol map (pair_map (Right fty)) f
    in
    map_fol map (pair_map (Right fty)) f 


let map_fol_pred = fun x -> map_fol_pred_ty (Fun.id) x

(** {2 Helpers to build locatable formulas} *)

let true_fol : ('a, 'b) fol = mk_dummy_loc FOL_True
let false_fol : ('a, 'b) fol = mk_dummy_loc FOL_False
let atomic_fol (x : 'a) : ('a, 'b) fol = mk_dummy_loc (FOL_Atom x)

let not_fol (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdUnary (LNot, f))

let and_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdBinary (f1, (LAnd), f2))

let or_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdBinary (f1, LOr, f2))

let equiv_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdBinary (f1, Equiv, f2))

let arrow_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdBinary (f1, Arrow, f2))

let forall_fol (vars : (string * 'qty) list) (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (Forall (vars, f))

let exists_fol (vars : (string * 'qty) list) (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (Exists (vars, f))
