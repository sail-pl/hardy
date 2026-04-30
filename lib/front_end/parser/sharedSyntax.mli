(** {1 Types shared between programs and logics} *)

(** Types *)

type base_ty =
    Ty_Int
    | Ty_Real
    | Ty_Bool
    | Ty_String
    | Ty_Array of base_ty * int option
    | Ty_Prod of base_ty list

type cat_ty = State | Input | Output | Local

type ty = cat_ty * base_ty option

val is_state : ty -> bool

val is_input : ty -> bool

val is_output : ty -> bool

type standard_logic_bop = Equiv | Arrow | LAnd | LOr | Program of string

type standard_logic_uop = LNot

module type BoolA =
sig
    type 'a t
    val pp :
        (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    type atom
    val conj : 'a t -> 'a t -> 'a t
    val disj : 'a t -> 'a t -> 'a t
    val tt : 'a t
    val ff : 'a t
    val neg : 'a t -> 'a t
    val atomic : atom -> 'a t
end

module Unit : sig type t = unit end

type 'a bool_a =
    True : 'a bool_a
    | False : 'a bool_a
    | Atom : 'a -> 'a bool_a
    | And : 'a bool_a * 'a bool_a -> 'a bool_a
    | Or : 'a bool_a * 'a bool_a -> 'a bool_a
    | Not : 'a bool_a -> 'a bool_a

val pp_boola : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a bool_a -> unit

val map_formula : ('a -> 'b) -> 'a bool_a -> 'b bool_a

val fold_formula : ('a bool_a -> 'b -> 'b) -> ('a -> 'b -> 'b) -> 'b -> 'a bool_a -> 'b

val pp_paren_atomic_boola : (Format.formatter -> 'a list -> unit) -> Format.formatter -> 'a list -> unit

val pp_cnf_boola : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a HardyMisc.Utils.cnf -> unit

val formula_depth : 'a bool_a -> int
