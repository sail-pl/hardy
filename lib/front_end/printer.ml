open HardyMisc.Utils
(** {1 Stringification of different datastructures}*)

open FrontParser
open SharedSyntax
open FOLSyntax
open LTLSyntax
open ProgramSyntax
open InstantSyntax

let pp_cat_ty fmt = function
  | Input -> Format.fprintf fmt "inputs"
  | Output -> Format.fprintf fmt "outputs"
  | State -> Format.fprintf fmt "state"
  | Local -> Format.fprintf fmt "local"

let rec pp_base_ty fmt = function
  | Ty_Bool -> Format.fprintf fmt "bool"
  | Ty_Int -> Format.fprintf fmt "int"
  | Ty_String -> Format.fprintf fmt "string"
  | Ty_Array (ty, _) -> Format.fprintf fmt "array %a" pp_base_ty ty
  | Ty_Prod l -> Format.(fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "*") pp_base_ty) l)

let pp_ty fmt (c, t) = Format.fprintf fmt "%a.%a" pp_cat_ty c pp_base_ty t

let pp_unop fmt (op : common_logic_unary) =
  match op with Not -> Format.fprintf fmt "!"

let pp_binop fmt (op : arithm_binop) =
  Format.fprintf fmt
    (match op with
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
    | And -> "&&")

let pp_common_logic_binary fmt : common_logic_binary -> unit = function
  | Equiv -> Format.fprintf fmt "<->"
  | Arrow -> Format.fprintf fmt "->"
  | Arithm o -> pp_binop fmt o

let pp_hist fmt (v, h) =
  match h with
  | Some (Previous 0) | None -> Format.fprintf fmt "%s" v
  | Some (Previous n) -> Format.fprintf fmt "prev %i %s" n v
  | Some (At n) -> Format.fprintf fmt "%s at %i" v n

let pp_paren_exp fmt f e =
  match e.value with BinOp _ -> Format.fprintf fmt "(%a)" f e | _ -> f fmt e

let rec pp_exp (print_var : _ -> _ * _ -> unit) fmt (e : 't expr) =
  let pp_exp fmt = pp_paren_exp fmt (pp_exp print_var) in
  match e.value with
  | Int n -> Format.fprintf fmt "%i" n
  | True -> Format.fprintf fmt "true"
  | False -> Format.fprintf fmt "false"
  | String s -> Format.fprintf fmt "%s" s
  | Array l ->
      Format.(
        fprintf fmt "[%a]"
          (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ";@ ") pp_exp)
          l)
  | Var (s, i) -> print_var fmt (s, i)
  | Not e -> Format.fprintf fmt "!%a" pp_exp e
  | ArrayCell v -> Format.fprintf fmt "%a[%a]" pp_exp v.array pp_exp v.idx
  | Prod [x] -> Format.fprintf fmt "%a" pp_exp x
  | Prod l -> Format.(fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") pp_exp) l)
  | BinOp v ->
      Format.fprintf fmt "%a %a %a" pp_exp v.left pp_binop v.op pp_exp v.right

let pp_paren_fol f1 f2 fmt (p : _ fol) =
  match p.value with
  | FOL_Binary _ -> Format.fprintf fmt "(%a)" f1 p
  | Pred e -> pp_paren_exp fmt f2 e
  | _ -> f1 fmt p

let rec pp_fol (pp_ty : Format.formatter -> ty -> unit) fmt
    (f : (instant option expr, 'a) fol) =
  let open Format in
  let pp_id_ty =
    Format.pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt "@ ")
      (fun fmt (id, ty) -> Format.fprintf fmt "(%s:%a)" id pp_ty ty)
  in
  let pp_fol' = pp_paren_fol (pp_fol pp_ty) (pp_exp pp_hist) in

  match f.value with
  | FOL_True -> Format.fprintf fmt "true"
  | FOL_False -> Format.fprintf fmt "false"
  | Pred e -> pp_exp pp_hist fmt e
  | FOL_Unary (op, f) -> Format.fprintf fmt "%a %a" pp_unop op pp_fol' f
  | FOL_Binary (f1, op, f2) ->
      Format.fprintf fmt "%a %a %a" pp_fol' f1 pp_common_logic_binary op pp_fol'
        f2
  | Forall (idty, f) ->
      Format.fprintf fmt "forall %a. %a" pp_id_ty idty (pp_fol pp_ty) f
  | Exists (idty, f) ->
      Format.fprintf fmt "exists %a. %a" pp_id_ty idty (pp_fol pp_ty) f
  | ExistsPrev (id, f) ->
      Format.fprintf fmt "exists_prev %s. %a" id (pp_fol pp_ty) f

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
