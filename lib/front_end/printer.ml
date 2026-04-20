open FrontParser
open HardyMisc.Utils
open SharedSyntax
open FOLSyntax
open LTLSyntax
open PLTLSyntax
open ProgramSyntax
open InstantSyntax
open Format
 
let pp_cat_ty fmt = function
  | Input -> fprintf fmt "inputs"
  | Output -> fprintf fmt "outputs"
  | State -> fprintf fmt "state"
  | Local -> fprintf fmt "local"

let rec pp_base_ty fmt = function
  | Ty_Bool -> Format.fprintf fmt "bool" 
  | Ty_Int -> Format.fprintf fmt "int" 
  | Ty_Real -> Format.fprintf fmt "real" 
  | Ty_String -> Format.fprintf fmt "string"
  | Ty_Array (ty,_) -> Format.fprintf fmt "array %a" pp_base_ty ty
  | Ty_Prod l -> Format.(fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "*") pp_base_ty) l)
  
let pp_ty fmt (c, t) = fprintf fmt "%a.%a" pp_cat_ty c pp_base_ty t

let pp_unop fmt (op : standard_logic_uop) =
  match op with LNot -> fprintf fmt "!"

let pp_expr_binop fmt (op : expr_binop) =
  fprintf fmt
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

let pp_common_logic_binary fmt (op: standard_logic_bop) : unit = 
  fprintf fmt (match op with
  | Equiv -> "<->"
  | Arrow -> "->"
  | LOr ->  "||"
  | LAnd ->  "&&"
  )

let pp_hist fmt (v, h) =
  match h with
  | Some (Previous 0) | None -> pp_print_string fmt v
  | Some (Previous n) -> fprintf fmt "prev %i %s" n v
  | Some (At n) -> fprintf fmt "%s at %i" v n

(* let pp_nohist fmt (id,_) = pp_print_string fmt id *)

let [@warning "-4"] pp_paren_exp f fmt e =
  match e.value with BinOp _ -> fprintf fmt "(%a)" f e | _ -> f fmt e

let rec pp_exp (print_var : _ -> _ * _ -> unit) fmt (e : 't expr) =
  let pp_exp = pp_paren_exp (pp_exp print_var) in
  match e.value with
  | Int n -> fprintf fmt "%i" n
  | Real r -> fprintf fmt "%s.%s%a" r.num r.frac (pp_print_option pp_print_string) r.exp
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
  | Var (s, i) -> print_var fmt (s, i)
  | UnOp (ENot,e) -> fprintf fmt "!%a" pp_exp e
  | BinOp v ->
      fprintf fmt "%a %a %a" pp_exp v.left pp_expr_binop v.op pp_exp v.right
  | String s -> Format.fprintf fmt "%s" s
  | Array l -> Format.(fprintf fmt "[%a]" (pp_print_array ~pp_sep:(fun fmt () -> fprintf fmt ";@ ") pp_exp) (Iarray.to_array l))
  | ArrayCell v -> Format.fprintf fmt "%a[%a]" pp_exp v.array pp_exp v.idx
  | Prod [x] -> Format.fprintf fmt "%a" pp_exp x
  | Prod l -> Format.(fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") pp_exp) l)
  
let [@warning "-4"] pp_paren_fol pp_fol pp_atom fmt (p : _ fol) =
  match p.value with
  | FOL_StdBinary _ -> fprintf fmt "(%a)" pp_fol p
  | FOL_Atom e -> pp_atom fmt e
  | _ -> pp_fol fmt p
  

let rec pp_fol : 'a. (formatter -> 'a -> unit) -> _ -> _ -> ('a,'b) fol -> _ =
    fun pp_atom pp_ty fmt f ->
  let open Format in
  let pp_id_ty =
    pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt "@ ")
      (fun fmt (id, ty) -> fprintf fmt "(%s:%a)" id pp_ty ty)
  in
  let pp_fol' = pp_paren_fol (pp_fol pp_atom pp_ty) pp_atom in

  match f.value with
  | FOL_True -> fprintf fmt "true"
  | FOL_False -> fprintf fmt "false"
  | FOL_Atom e -> pp_atom fmt e
  | FOL_StdUnary (op, f) -> fprintf fmt "%a %a" pp_unop op pp_fol'  f
  | FOL_StdBinary (f1, op, f2) ->
      fprintf fmt "%a %a %a" pp_fol'  f1 pp_common_logic_binary op pp_fol' 
        f2
  | FOL_StdNary (op, l) ->
      pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "%a" pp_common_logic_binary op) (fun fmt arg -> pp_fol' fmt arg) fmt l
  | Forall (idty, f) ->
      fprintf fmt "forall %a. %a" pp_id_ty idty pp_fol' f
  | Exists (idty, f) ->
      fprintf fmt "exists %a. %a" pp_id_ty idty pp_fol' f
  (* | ExistsPrev q ->
      fprintf fmt "exists_prev %s as %s. %a" q.h_var q.binder pp_fol' q.f
  | ForallPrev q ->
      fprintf fmt "exists_prev %s as %s. %a" q.h_var q.binder pp_fol' q.f *)

  let pp_pred pp_atom fmt = 
    let open Format in
      function
    | Atom a -> pp_atom fmt a
    | Predicate {name;args} -> 
        fprintf fmt "%s(%a)" 
          name 
          (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") (fun fmt arg -> pp_atom fmt arg))
          args

let pp_ltl_binop fmt ( op: ltl_binary) : unit = 
  let op = match op with  
  | Until -> "U"
  | Release -> "R"
  | WeakUntil -> "W"
  | StrongRelease -> "M"
  | LTL_StdBinary op -> asprintf "%a" pp_common_logic_binary op
  in pp_print_string fmt op 

let pp_ltl_unop fmt  ( op: ltl_unary) : unit =
    let op = match op with  
  | Next -> "X"
  | Always -> "G"
  | Eventually -> "F"
  | LTL_StdUnary op -> asprintf "%a" pp_unop op
  in pp_print_string fmt op 


let pp_ltl_binop_spin fmt ( op: ltl_binary) : unit =
  let op = match op with  
  | Until -> "U"
  | Release -> "V"
  | LTL_StdBinary Arrow -> "->"
  | LTL_StdBinary LOr -> "||"
  | LTL_StdBinary LAnd -> "&&"
  | LTL_StdBinary Equiv -> "<->"
  | WeakUntil -> "W"
  | StrongRelease -> "M"
  in pp_print_string fmt op 

let pp_ltl_unnop_spin fmt ( op: ltl_unary) : unit =
  let op = match op with  
  | Next -> "X"
  | Always -> "[]"
  | Eventually -> "<>"
  | LTL_StdUnary LNot -> "!"
  in pp_print_string fmt op 




let pp_ltl (pp_atom : formatter -> 'a -> unit)
    (pp_ltl_binop : formatter -> ltl_binary -> unit)
    (pp_ltl_unop : formatter -> ltl_unary -> unit) : formatter -> 'a ltl -> unit = 
    let rec aux fmt f = 
    match f.value with
      | LTL_True -> pp_print_string fmt "true"
      | LTL_False -> pp_print_string fmt "false"
      | LTL_Atom p -> pp_atom fmt p
      | LTL_Binary (f1, op, f2) ->
          fprintf fmt "(%a) %a (%a)" aux f1 pp_ltl_binop op aux f2
      | LTL_Unary (op, f) ->
          fprintf fmt "%a(%a)" pp_ltl_unop op aux f
      in aux 


let pp_pltl_binop fmt ( op: pltl_binary) : unit = 
  let op = match op with  
  | Since -> "S"
  | WeakSince -> "Z"
  | PLTL_StdBinary op -> asprintf "%a" pp_common_logic_binary op
  in pp_print_string fmt op 

let pp_pltl_unop fmt  ( op: pltl_unary) : unit =
    let op = match op with  
  | Once -> "O"
  | Historically -> "H"
  | Yesterday -> "Y"
  | WeakYesterday -> "T" (* syntax from https://github.com/DoppeD/ppLTLTT/tree/main/ppLTLTT *)
  | PLTL_StdUnary op -> asprintf "%a" pp_unop op
  in pp_print_string fmt op 
  
let pp_ltl_default f = pp_ltl f pp_ltl_binop pp_ltl_unop


let pp_pltl (pp_atom : formatter -> 'a -> unit)
    (pp_pltl_binop : formatter -> pltl_binary -> unit)
    (pp_pltl_unop : formatter -> pltl_unary -> unit) : formatter -> 'a pltl -> unit = 
    let rec aux fmt f = 
    match f.value with
      | PLTL_True -> pp_print_string fmt "true"
      | PLTL_False -> pp_print_string fmt "false"
      | PLTL_Atom p -> pp_atom fmt p
      | PLTL_Binary (f1, op, f2) ->
          fprintf fmt "(%a) %a (%a)" aux f1 pp_pltl_binop op aux f2
      | PLTL_Unary (op, f) ->
          fprintf fmt "%a(%a)" pp_pltl_unop op aux f
      in aux 

let pp_pltl_default f = pp_pltl f pp_pltl_binop pp_pltl_unop