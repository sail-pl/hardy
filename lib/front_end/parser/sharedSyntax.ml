(** {1 Types shared between programs and logics} *)

(** Types *)

type base_ty = Ty_Int | Ty_Bool | Ty_String | Ty_Array of base_ty * int
type cat_ty = State | Input | Output | Local
type ty = cat_ty * base_ty

(** Standard Operators *)

type arithm_binop = Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq | Neq | And | Or
type common_logic_unary = Not
type common_logic_binary = Equiv | Arrow | Arithm of arithm_binop
