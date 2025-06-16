(** {1 Types shared between programs and logics} *)

(** Types *)

type base_ty = Ty_Int | Ty_Bool | Ty_String | Ty_Array of base_ty * int
type cat_ty = State | Input | Output | Local
type ty = cat_ty * base_ty

(** Standard Logic Operators *)

type standard_logic_bop = Equiv | Arrow | LAnd | LOr
type standard_logic_uop = LNot
