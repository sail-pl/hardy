open FrontParser
open HardyMisc.Utils
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

let pp_unop fmt (op : standard_logic_uop) =
  match op with LNot -> Format.fprintf fmt "!"

let pp_expr_binop fmt (op : expr_binop) =
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
    | EOr -> "||"
    | EAnd -> "&&")

let pp_common_logic_binary fmt (op : standard_logic_bop) : unit =
  Format.fprintf fmt
    (match op with
    | Equiv -> "<->"
    | Arrow -> "->"
    | LOr -> "||"
    | LAnd -> "&&")

let pp_hist fmt (v, h) =
  match h with
  | Some (Previous 0) | None -> Format.pp_print_string fmt v
  | Some (Previous n) -> Format.fprintf fmt "prev %i %s" n v
  | Some (At n) -> Format.fprintf fmt "%s at %i" v n

let pp_nohist fmt (id, _) = Format.pp_print_string fmt id

let pp_paren_exp fmt f e =
  match e.value with BinOp _ -> Format.fprintf fmt "(%a)" f e | _ -> f fmt e

let rec pp_exp (print_var : _ -> _ * _ -> unit) fmt (e : 't expr) =
  let pp_exp fmt = pp_paren_exp fmt (pp_exp print_var) in
  match e.value with
  | Int n -> Format.fprintf fmt "%i" n
  | True -> Format.fprintf fmt "true"
  | False -> Format.fprintf fmt "false"
  | Var (s, i) -> print_var fmt (s, i)
  | UnOp (ENot, e) -> Format.fprintf fmt "!%a" pp_exp e
  | BinOp v ->
      Format.fprintf fmt "%a %a %a" pp_exp v.left pp_expr_binop v.op pp_exp
        v.right
  | String s -> Format.fprintf fmt "%s" s
  | Array l ->
      Format.(
        fprintf fmt "[%a]"
          (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ";@ ") pp_exp)
          l)
  | ArrayCell v -> Format.fprintf fmt "%a[%a]" pp_exp v.array pp_exp v.idx
  | Prod [x] -> Format.fprintf fmt "%a" pp_exp x
  | Prod l -> Format.(fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") pp_exp) l)

let pp_paren_fol f1 f2 fmt (p : _ fol) =
  match p.value with
  | FOL_StdBinary _ -> Format.fprintf fmt "(%a)" f1 p
  | FOL_Atom e -> pp_paren_exp fmt f2 e
  | _ -> f1 fmt p

let rec pp_fol (pp_exp : Format.formatter -> _ expr -> unit)
    (pp_ty : Format.formatter -> ty -> unit) fmt (f : (_ expr, 'a) fol) =
  let open Format in
  let pp_id_ty =
    Format.pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt "@ ")
      (fun fmt (id, ty) -> Format.fprintf fmt "(%s:%a)" id pp_ty ty)
  in
  let pp_fol' = pp_paren_fol (pp_fol pp_exp pp_ty) pp_exp in

  match f.value with
  | FOL_True -> Format.fprintf fmt "true"
  | FOL_False -> Format.fprintf fmt "false"
  | FOL_Atom e -> pp_exp fmt e
  | FOL_StdUnary (op, f) -> Format.fprintf fmt "%a %a" pp_unop op pp_fol' f
  | FOL_StdBinary (f1, op, f2) ->
      Format.fprintf fmt "%a %a %a" pp_fol' f1 pp_common_logic_binary op pp_fol'
        f2
  | Forall (idty, f) ->
      Format.fprintf fmt "forall %a. %a" pp_id_ty idty (pp_fol pp_exp pp_ty) f
  | Exists (idty, f) ->
      Format.fprintf fmt "exists %a. %a" pp_id_ty idty (pp_fol pp_exp pp_ty) f
  | ExistsPrev (id, f) ->
      Format.fprintf fmt "exists_prev %s. %a" id (pp_fol pp_exp pp_ty) f

let string_of_ltl_binop : ltl_binary -> string = function
  | Until -> "U"
  | Release -> "R"
  | WeakUntil | StrongRelease -> failwith "unspported binop"
  | LTL_StdBinary op -> Format.asprintf "%a" pp_common_logic_binary op

let string_of_ltl_unop : ltl_unary -> string = function
  | Next -> "X"
  | Always -> "G"
  | Eventually -> "F"
  | LTL_StdUnary op -> Format.asprintf "%a" pp_unop op

let string_of_ltl (string_of_atom : 'a -> string)
    (string_of_ltl_binop : ltl_binary -> string)
    (string_of_ltl_unop : ltl_unary -> string) : 'a ltl -> string =
  let rec aux f =
    match f.value with
    | LTL_True -> "true"
    | LTL_False -> "false"
    | LTL_Atom p -> string_of_atom p
    | LTL_Binary (f1, op, f2) ->
        let f1 = aux f1 in
        let f2 = aux f2 in
        Format.sprintf "(%s) %s (%s)" f1 (string_of_ltl_binop op) f2
    | LTL_Unary (op, f) ->
        let f = aux f in
        Format.sprintf "%s(%s)" (string_of_ltl_unop op) f
  in
  aux
