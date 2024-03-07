type arithm_binop = Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq
type common_logic_unary = Not

type common_logic_binary =
  | Xor
  | Equiv
  | Or
  | And
  | Arrow
  | Arithm of arithm_binop
