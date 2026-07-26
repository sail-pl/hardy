module PH = Why3.Ptree_helpers
module P = Why3.Ptree

open FrontParser.SharedSyntax

(** {1 Helpers to construct a Why3 Program and its specification} *)

(** {2 Values and Types Management} *)

val get_cat_ty : cat_ty -> string
(** [get_cat_ty c] returns the name of the type category [c] (inputs,outputs, state or local) *)

(** [get_custom_pty s] returns the user-defined Why3 type named [s]*)
val get_custom_pty : string -> Why3.Ptree.pty

(** [get_pty ty] returns the Why3 type corresponding to the program type [ty] *)
val get_pty : base_ty -> Why3.Ptree.pty

(** effectful bindings to maintain correspondance between variable id and its category and type *)
val bindings : (string, ty) Hashtbl.t

(** [add_user_binding (id,ty)] updates the bindings with the provided name [id] and type [ty] *)
val add_user_binding : string * ty -> unit

(** [add_bindings seq] updates the bindings with a sequence [seq] of pair of name and type (including its category)*)
val add_bindings : (string * ty) Seq.t -> unit

(** [add_local_bindings seq] updates the bindings with a sequence [seq] of pair of name and program type, using the [Local] category *)
val add_local_bindings :
  (string * base_ty option) Seq.t -> unit

(** [remove_bindings seq] removes the list of identifiers [seq] from the bindings *)
val remove_bindings : string Seq.t -> unit

val get_binding_type : string -> (ty -> 'a) -> 'a

val ty_suffix : string -> string

val get_pp_string : (Format.formatter -> 'a -> unit) -> 'a -> string



(** {2 History Instrumentation} *)

(** Why3 name for the (ghost) history *)
val history_id : string

(** Why3 term for getting the history length *)
val history_length : Why3.Ptree.term

(** [instant_field cat] returns the Why3 record field name associated to the category [cat] *)
val instant_field : cat_ty -> string

(** [nth_h cat] returns the name of the ghost function that relates previous values of variables of category [cat]   *)
val nth_h : cat_ty -> string


(** {2 Terms and Expressions Builders} *)  


val translate_rexpr : ty expr -> P.expr

(** [translate_binop app infix op e1 e2] construct an expression corresponding to the application of the binary operator [op] to [e1] and [e2].
    [app] is used when the operator is seen as a function application and [infix] when it is seen as an infix operator
*)
val translate_binop :
  (P.qualid -> 'a list -> 'b) ->
  (Why3.Ptree.ident -> 'a -> 'a -> 'b) ->
  expr_binop -> 'a -> 'a -> 'b


(** [pterm_of_fol atom_tr f] returns the Why3 term corresponding to the FOL formula [f], using
  [atom_tr] to translate the formula's atoms *)
val pterm_of_fol :
  ('a expr -> P.term) ->
  ('a expr FrontParser.FOLSyntax.predicate,
   base_ty option)
  FrontParser.FOLSyntax.fol -> P.term