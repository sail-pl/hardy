(** {1 Types shared between programs and logics} *)

(** Types *)

type base_ty = Ty_Int | Ty_Bool
type cat_ty = State | Input | Output | Local
type ty = cat_ty * base_ty

(** Standard Operators *)

type arithm_binop = Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq | Neq
type common_logic_unary = Not
type common_logic_binary = Equiv | Or | And | Arrow | Arithm of arithm_binop
