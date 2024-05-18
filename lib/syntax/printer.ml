open Locations
open Types
open Operators
open Fol
open Ltl
open Syntax

let string_of_ty = function Ty_Bool -> "bool" | Ty_Int -> "int"
let string_of_unop : common_logic_unary -> string = function Not -> "~"

let string_of_binop : arithm_binop -> string = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Gt -> ">"
  | Lt -> "<"
  | Gte -> ">="
  | Lte -> "<="
  | Eq -> "="

let string_of_common_logic_binary : common_logic_binary -> string = function
  | Xor -> "^"
  | Equiv -> "<->"
  | Or -> "OR"
  | And -> "AND"
  | Arrow -> "->"
  | Arithm o -> string_of_binop o

let rec string_of_exp (e : expr) : string =
  match e.value with
  | Int n -> string_of_int n
  | True -> "true"
  | False -> "false"
  (* | Old s -> Format.sprintf "old(%s)" s *)
  | Var s | Read s -> s
  | BinOp (e1, op, e2) ->
      Format.sprintf "(%s) %s (%s)" (string_of_exp e1) (string_of_binop op)
        (string_of_exp e2)

let rec string_of_fol (f : expr fol) : string =
  let open Format in
  let print_idty idty =
    String.concat " "
      (List.map
         (fun (id, ty) -> Format.sprintf "(%s:%s)" id (string_of_ty ty))
         idty)
  in

  match f.value with
  | FOL_True -> "true"
  | FOL_False -> "false"
  | Pred e -> string_of_exp e
  | FOL_Unary (op, f) -> sprintf "%s (%s)" (string_of_unop op) (string_of_fol f)
  | FOL_Binary (f1, op, f2) ->
      sprintf "(%s) %s (%s)" (string_of_fol f1)
        (string_of_common_logic_binary op)
        (string_of_fol f2)
  | Forall (idty, f) ->
      sprintf "forall %s. %s" (print_idty idty) (string_of_fol f)
  | Exists (idty, f) ->
      asprintf "exists %s. %s" (print_idty idty) (string_of_fol f)

let string_of_ltl_binop : ltl_binary -> string = function
  | Until -> "U"
  | Release -> "R"
  | LTL_BArithm Arrow -> "->"
  | LTL_BArithm Or -> "||"
  | LTL_BArithm And -> "&&"
  | LTL_BArithm Equiv -> "<->"
  | _ -> failwith "unsupported bop"

let string_of_ltl_unop : ltl_unary -> string = function
  | Next -> "X"
  | Always -> "G"
  | Eventually -> "F"
  | LTL_UArithm Not -> "!"
  | WeakNext -> failwith "unsupported unop"

let string_of_ltl (string_of_pred : expr fol -> string)
    (string_of_ltl_binop : ltl_binary -> string)
    (string_of_ltl_unop : ltl_unary -> string) : expr fol ltl -> string =
  let rec aux f =
    match f.value with
    | LTL_True -> "true"
    | LTL_False -> "false"
    | LTL_Pred p -> string_of_pred p
    | LTL_Binary (f1, op, f2) ->
        let f1 = aux f1 in
        let f2 = aux f2 in
        Format.sprintf "(%s) %s (%s)" f1 (string_of_ltl_binop op) f2
    | LTL_Unary (op, f) ->
        let f = aux f in
        Format.sprintf "%s (%s)" (string_of_ltl_unop op) f
  in
  aux
