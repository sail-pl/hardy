open HardyMisc.Utils
(** {1 Stringification of different datastructures}*)

open FrontParser
open SharedSyntax
open FOLSyntax
open LTLSyntax
open ProgramSyntax
open InstantSyntax

let string_of_cat_ty = function
  | Input -> "inputs"
  | Output -> "outputs"
  | State -> "state"
  | Local -> "local"

let string_of_base_ty = function Ty_Bool -> "bool" | Ty_Int -> "int"
let string_of_ty (c, t) = string_of_cat_ty c ^ "." ^ string_of_base_ty t
let string_of_unop : common_logic_unary -> string = function Not -> "!"

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
  | Neq -> "<>"
  | Or -> "||"
  | And -> "&&"

let string_of_common_logic_binary : common_logic_binary -> string = function
  | Equiv -> "<->"
  | Arrow -> "->"
  | Arithm o -> string_of_binop o

let string_of_hist (v, h) =
  match h with
  | Some (Previous 0) | None -> v
  | Some (Previous n) -> Printf.sprintf "prev %i %s" n v
  | Some (At n) -> Printf.sprintf "%s at %i" v n


let paren_exp f e = match e.value with BinOp _ -> Format.sprintf "(%s)" (f e) | _ -> f e

let rec string_of_exp (f : string * 't -> string) (e : 't expr)  : string =
  let string_of_exp = paren_exp (string_of_exp f) in
  match e.value with
  | Int n -> string_of_int n
  | True -> "true"
  | False -> "false"
  | Var (s, i) -> f (s, i)
  | Read s -> s
  | Not e -> Format.sprintf "!%s" (string_of_exp e)
  | BinOp (e1, op, e2) ->
      Format.sprintf "%s %s %s" (string_of_exp e1) (string_of_binop op)
        (string_of_exp e2)


let paren_fol f1 f2 (p:_ fol) = match p.value with 
  | FOL_Binary _ -> Format.sprintf "(%s)" (f1 p) 
  | Pred e -> paren_exp f2 e
  | _ -> f1 p

let rec string_of_fol (string_of_ty : 'a -> string) (f : (instant option expr, 'a) fol)
   : string =
  let open Format in
  let print_idty idty =
    String.concat " "
      (List.map
         (fun (id, ty) -> Format.sprintf "(%s:%s)" id (string_of_ty ty))
         idty)
  in
  let string_of_fol' = paren_fol (string_of_fol string_of_ty) (string_of_exp string_of_hist) in

  match f.value with
  | FOL_True -> "true"
  | FOL_False -> "false"
  | Pred e -> string_of_exp string_of_hist e
  | FOL_Unary (op, f) ->
      sprintf "%s %s" (string_of_unop op) (string_of_fol' f)
  | FOL_Binary (f1, op, f2) ->
      sprintf "%s %s %s"
        (string_of_fol' f1)
        (string_of_common_logic_binary op)
        (string_of_fol' f2)
  | Forall (idty, f) ->
      sprintf "forall %s. %s" (print_idty idty) (string_of_fol string_of_ty f)
  | Exists (idty, f) ->
      asprintf "exists %s. %s" (print_idty idty) (string_of_fol string_of_ty f)
  | ExistsPrev (id, f) ->
        asprintf "exists_prev %s. %s" id (string_of_fol string_of_ty f)

let string_of_ltl_binop : ltl_binary -> string = function
  | Until -> "U"
  | Release -> "R"
  | LTL_BArithm Arrow -> "->"
  | LTL_BArithm (Arithm Or) -> "||"
  | LTL_BArithm (Arithm And) -> "&&"
  | LTL_BArithm Equiv -> "<->"
  | _ -> failwith "unsupported bop"

let string_of_ltl_unop : ltl_unary -> string = function
  | Next -> "X"
  | Always -> "G"
  | Eventually -> "F"
  | LTL_UArithm Not -> "!"

let string_of_ltl (string_of_pred : 'a -> string)
    (string_of_ltl_binop : ltl_binary -> string)
    (string_of_ltl_unop : ltl_unary -> string) : 'a ltl -> string =
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
