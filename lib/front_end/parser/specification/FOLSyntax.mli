(** {1 Terms for First Order Logic} *)


type ('a, 'qty) fol = ('a, 'qty) fol_ HardyMisc.Utils.locatable
(** First order Logic formulas parameterized by atomic propositions *)


and ('a, 'qty) fol_ =
    FOL_True
  | FOL_False
  | FOL_Atom of 'a
  | FOL_StdUnary of SharedSyntax.standard_logic_uop * ('a, 'qty) fol
  | FOL_StdBinary of ('a, 'qty) fol * SharedSyntax.standard_logic_bop *
      ('a, 'qty) fol
  | FOL_StdNary of SharedSyntax.standard_logic_bop * ('a, 'qty) fol list
  | Forall of (string * 'qty) list * ('a, 'qty) fol
  | Exists of (string * 'qty) list * ('a, 'qty) fol
  | ForallPrev of  ('a, 'qty) prev_quant (* temporal universal quantification *)
  | ExistsPrev of('a, 'qty) prev_quant (* temporal existential quantification *)

and ('a, 'qty) prev_quant = {
  h_var : string;
  binder : string;
  f : ('a, 'qty) fol;
}

type 'a predicate =
    Atom of 'a
    | Predicate of { name : string; args : 'a list; }

val map_pred : ('a -> 'b) -> 'a predicate -> 'b predicate

type ('a, 'qty) pred_fol = ('a predicate, 'qty) fol

type 'qty pred_decl = {
    name : string;
    params : string list;
    body : (string, 'qty) fol;
}

(** [map_fol m m_atom m_ty form ] *)
val map_fol : (('a, 'ty_a) fol -> ('b, 'ty_b) fol) ->
              ('a -> 'b) -> (string * 'ty_a -> string * 'ty_b) -> ('a, 'ty_a) fol -> ('b, 'ty_b) fol

(** [fold_fol j pj init form] *)
val fold_fol :
    ('b -> ('a, 't) fol -> 'b) -> ('b -> 'a -> 'b) -> 'b -> ('a, 't) fol -> 'b

(** [map_fol_ty m f] replaces every quantifer [Exists (l,e)] and [Forall (l,e)] *)
val map_fol_ty : (string * 'a -> string * 'b) -> ('c, 'a) fol -> ('c, 'b) fol


(** [map_fol_pred fty m f] replaces every variable types [t] with [fty t] and replaces every atom [x] of [f] by [m x] *)
val map_fol_pred_ty :
    ('ty_a -> 'ty_b) ->
    ('a -> 'b) -> ('a predicate, 'ty_a) fol -> ('b predicate, 'ty_b) fol

(** [map_fol_pred m f] replaces every atom [x] of [f] by [m x] *)
val map_fol_pred :
    ('a -> 'b) -> ('a predicate, 'c) fol -> ('b predicate, 'c) fol

(** {2 Helpers to build locatable formulas} *)

val true_fol : ('a, 'b) fol

val false_fol : ('a, 'b) fol

val atom_fol : 'a -> ('a, 'b) fol

val not_fol : ('a, 'b) fol -> ('a, 'b) fol

val and_fol : ('a, 'b) fol -> ('a, 'b) fol -> ('a, 'b) fol

val or_fol : ('a, 'b) fol -> ('a, 'b) fol -> ('a, 'b) fol

val equiv_fol : ('a, 'b) fol -> ('a, 'b) fol -> ('a, 'b) fol

val arrow_fol : ('a, 'b) fol -> ('a, 'b) fol -> ('a, 'b) fol

val forall_fol : (string * 'qty) list -> ('a, 'qty) fol -> ('a, 'qty) fol

val exists_fol : (string * 'qty) list -> ('a, 'qty) fol -> ('a, 'qty) fol

val fol_of_bool_a : ('a -> ('b, 'c) fol) -> 'a SharedSyntax.bool_a -> ('b, 'c) fol

val fol_of_cnf : ('a -> ('a, 'b) fol) ->
                'a HardyMisc.Utils.cnf -> ('a, 'b) fol HardyMisc.Utils.cnf
