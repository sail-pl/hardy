open HardyMisc.Utils


(** Program Expressions *)

type expr_uop = ENot
type expr_binop = Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq | Neq | EAnd | EOr

type ('ext, 't) expr = ('ext, 't) expression_ locatable
(** variables can carry extra information of type ['t] and extra expressions of type ['ext] can be added (todo: extensible variants?)*)

and ('ext, 't) expression_ =
  | Int of int
  | Real of {radix:int ; num:string ; frac:string  ; exp:string option}
  | True
  | False
  | Var of string * 't
  | UnOp of expr_uop * ('ext, 't) expr
  | BinOp of {left: ('ext, 't) expr ; op: expr_binop ; right : ('ext, 't) expr}
  | ArrayCell of {array: ('ext, 't) expr; idx: ('ext, 't) expr}
  | Array of ('ext, 't) expr iarray
  | String of string
  | Prod of ('ext, 't) expr list
  | Ext of 'ext


val string_of_pgrm_op : expr_binop -> string  
(** convert program binary operators to strings *)


val fold_expr : ('ext -> 'a) -> ('a -> ('ext,'t) expr -> 'a) -> 'a -> ('ext,'t) expr -> 'a


val map_expr : ('ext1 -> 'ext2) -> (('ext2,'t2) expr -> ('ext2,'t2) expr) -> (string * 't1 -> string * 't2) -> ('ext1,'t1) expr -> ('ext2,'t2) expr 

  
val expr_vars : ('ext -> (string * 't) list) -> (string * 't) list -> ('ext,'t) expr -> (string * 't) list


(** {1 Types shared between programs and logics} *)


type 'spec hoare_pair = { pre : 'spec; post : 'spec }

type ('spec, 'data) hoare_triple = ('spec hoare_pair, 'data) labeled

val map_triple_data : ('a -> 'b) -> ('c, 'a) labeled -> ('c, 'b) labeled

(** generic hoare pre/post pair *)

type 'v variant = { variant : 'v }

val variant : 'a variant -> 'a 

val mk_variant : 'a -> 'a variant

(** [private_var x] renames variable id [x] to a name that cannot have been
    declared by the user *)
val pp_private : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit

val private_var : string -> string

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


(** Standard Logic Operators *)

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
    | BA_True : 'a bool_a
    | BA_False : 'a bool_a
    | BA_Atom : 'a -> 'a bool_a
    | BA_And : 'a bool_a * 'a bool_a -> 'a bool_a
    | BA_Or : 'a bool_a * 'a bool_a -> 'a bool_a
    | BA_Not : 'a bool_a -> 'a bool_a

val pp_boola : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a bool_a -> unit

val map_formula : ('a -> 'b) -> 'a bool_a -> 'b bool_a

val fold_formula : ('a bool_a -> 'b -> 'b) -> ('a -> 'b -> 'b) -> 'b -> 'a bool_a -> 'b

val pp_paren_atomic_boola : (Format.formatter -> 'a list -> unit) -> Format.formatter -> 'a list -> unit

val pp_cnf_boola : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a HardyMisc.Utils.cnf -> unit

val formula_depth : 'a bool_a -> int

(* high-level program temporal specification *)
type ('temp_spec, 'spec_data, 'p) prog_with_spec = {prog_spec: ('temp_spec list,'spec_data) hoare_triple ; prog : 'p}
