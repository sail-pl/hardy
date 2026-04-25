(** maintains a correspondance between an atom and its associated unique
    identifier *)
module type S =
  sig
    type 'a t
    val map : ('a -> 'b) -> 'a t -> 'b t
    val join : 'a t t -> 'a t
    type data
    type atom

    val get_atom : string t -> (string * atom) t
    (** [get_atom i] returns the short name and the atom corresponding to the identifier [i] *)

    val subst : string t -> string t
    (** [subst f ty_to_str] replaces each atoms in formula [f] by a
    printing-friendly string where the types inside the atoms are replaced by
    [f_ty_to_str] *)

    val register_atom : atom t -> (string * string) t
    (** [register_atom a] returns the short and long identifier corresponding to the
      atom [a], creating fresh ones if they do not exist  *)


    val get_atom_ids : atom t -> (string * string) t
    (** [get_atom_ids a] returns the short and long identifier corresponding to the
      atom [a], that is required to have been previously registered *)

    val get_data : string -> data t
    val set_data : string -> data -> unit t
end


(** [sub_atom_in_str subst s] matches all atoms inside string [s]. Each atom [a]
    is then replaced by [subst a] *)
val sub_atom_in_str : (string -> string) -> string -> string

(** [atom_of_atom_id a] extracts the atom from the identifier [a]*)
val atom_of_atom_id : string -> int

(** [remove_exp_loc e] replaces all locations of expression [e] with None *)
val remove_exp_loc :
  't FrontParser.ProgramSyntax.expr -> 't FrontParser.ProgramSyntax.expr

(** Imperative instantiation of the atom signature [S] parameterized by the type [Data.t] of data an atom can hold and the type [Atom.t] of the atom  *)
module Imperative :
(Data : HardyMisc.Utils.SIMP_TYPE)
(Atom : HardyMisc.Utils.PRETTY_SIMP_TYPE) -> S   
  with type atom = Atom.t and
  type 'a t = 'a and
  type data = Data.t and
  type atom = Atom.t
