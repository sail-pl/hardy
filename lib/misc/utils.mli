(** {1 Misc Utilities} *)

module type SIMP_TYPE = sig type t end

module type TYPE = sig type 'a t end

module type PRETTY_SIMP_TYPE =
  sig type t val pp : Format.formatter -> t -> unit end

module type PRETTY_TYPE =
  sig
    type 'a t
    val pp :
      (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  end

module type FUNCTOR = sig type 'a t val map : ('a -> 'b) -> 'a t -> 'b t end

module type MONADIC =
  sig
    type 'a t
    val map : ('a -> 'b) -> 'a t -> 'b t
    val join : 'a t t -> 'a t
end

(** Token Location *)

type ('v, 'l) labeled = { value : 'v; label : 'l; }

type loc = Lexing.position * Lexing.position

type 'v locatable = ('v, loc option) labeled

val mk_labeled : label:'a -> 'b -> ('b, 'a) labeled

val map_value : ('a -> 'b) -> ('a, 'c) labeled -> ('b, 'c) labeled

val map_label : ('a -> 'b) -> ('c, 'a) labeled -> ('c, 'b) labeled

val dummy_pos : loc

val mk_dummy_loc : 'a -> ('a, 'b option) labeled

(** type alias for list of disjunctive and conjunctive formulas *)

type 'f disjunction = { disjuncts : 'f list; }

val mk_disj : 'a list -> 'a disjunction

val disj_singleton : 'a -> 'a disjunction

val map_disjuncts : ('a -> 'b) -> 'a disjunction -> 'b disjunction

val add_disjunct : 'a -> 'a disjunction -> 'a disjunction

val append_disjuncts : 'a disjunction -> 'a disjunction -> 'a disjunction

val disj_empty : 'a disjunction

type 'f conjunction = { conjuncts : 'f list; }

val mk_conj : 'a list -> 'a conjunction

val map_conjuncts : ('a -> 'b) -> 'a conjunction -> 'b conjunction

val conj_singleton : 'a -> 'a conjunction

val conj_empty : 'a conjunction

val add_conjunct : 'a -> 'a conjunction -> 'a conjunction

val append_conjuncts : 'a conjunction -> 'a conjunction -> 'a conjunction

type 'a cnf = 'a disjunction conjunction

(** [fold_mjoin f j init l] returns [init] if [l = nil], [f x] if [l] = [x] and
    otherwise, behaves like [List.fold_left] where the current value is applied
    to [f] before being applied with the accumulator to [j]. In the latter case,
    the initial value [init] is replaced by [j] applied to the first two
    elements.

    This function is useful to prevent extra terms in formulas: Instead of
    {m true \wedge x > 3}, we directly get {m x > 3}. *)
val fold_mjoin : ('a -> 'b) -> ('b -> 'b -> 'b) -> 'b -> 'a list -> 'b

(** Infix function composition *)
val ( << ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val ( >> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c

type (_, _, _, _) pair_app =
    | Left : ('a -> 'c) -> ('a, 'b, 'c, 'b) pair_app
    | Right : ('b -> 'd) -> ('a, 'b, 'a, 'd) pair_app
    | Both : ('a -> 'c) * ('b -> 'd) -> ('a, 'b, 'c, 'd) pair_app

(** function application to a pair *)
val pair_map : ('i1, 'i2, 'o1, 'o2) pair_app -> 'i1 * 'i2 -> 'o1 * 'o2

val add_opt_to_list : 'a option -> 'a list -> 'a list

module Bindings : module type of Map.Make(String)