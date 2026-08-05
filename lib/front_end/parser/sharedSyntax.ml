open HardyMisc.Utils


type 'spec hoare_pair = { pre : 'spec; post : 'spec }

type ('spec, 'data) hoare_triple = ('spec hoare_pair, 'data) labeled

let map_triple_data f t = {t with label=f t.label}


type 'v variant = { variant : 'v }

let mk_variant x : _ variant = { variant = x }
let variant x = x.variant

let pp_private (f : Format.formatter -> 'a -> unit) : Format.formatter -> 'a -> unit = 
  fun fmt -> Format.fprintf fmt "_%a" f

let private_var = Format.asprintf "%a" (pp_private Format.pp_print_string)

type base_ty = Ty_Int | Ty_Real | Ty_Bool | Ty_String | Ty_Array of base_ty * int option | Ty_Prod of base_ty list
type cat_ty = State | Input | Output | Local
type ty = cat_ty * (base_ty option)

let is_state (c,_ : ty) : bool = c = State
let is_input (c,_ : ty) : bool = c = Input
let is_output (c,_ : ty) : bool = c = Output


type expr_uop = ENot
type expr_binop = Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq | Neq | EAnd | EOr

let string_of_pgrm_op : expr_binop -> string = function 
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
  | EAnd -> "&&"


type ('ext, 't) expr = ('ext, 't) expression_ locatable

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


let rec fold_expr : type a. ('ext -> a) -> (a -> ('ext, 't) expr -> a) -> a -> ('ext, 't) expr -> a =
 fun ej j init e ->
  let fold_expr = fold_expr ej j in
  match e.value with
  | Int _ | Real _ | True | False | Var _ | String _  -> j init e
  | UnOp (_,e1) -> j (fold_expr init e1 ) e
  | BinOp x -> j (fold_expr (fold_expr init x.right) x.left) e 
  | ArrayCell v -> j (fold_expr (fold_expr init v.idx) v.array) e 
  | Array arr -> Iarray.fold_left fold_expr init arr
  | Prod arr -> List.fold_left fold_expr init arr
  | Ext e -> ej e


let rec map_expr : type t1 t2 ext1 ext2. (ext1 -> ext2) -> ((ext2,t2) expr -> (ext2,t2) expr) -> (string * t1 -> string * t2) -> (ext1,t1) expr -> (ext2,t2) expr =
 fun m_ext m var_map e ->
  let map_expr = map_expr m_ext m var_map in 
  match e.value with
  | Int _ | Real _ | True | False | String _ as value -> m {e with value}
  | Var (id,v) -> let (id,v) = var_map (id,v) in m {e with value=Var (id,v)}
  | UnOp (op,e1) -> m { e with value = UnOp (op,map_expr e1)}
  | BinOp x ->
      m { e with value = BinOp { x with left=map_expr x.left; right=map_expr x.right} }
  | ArrayCell v -> let idx = map_expr v.idx and array = map_expr v.array in  m { e with value = ArrayCell {idx;array} }
  | Array arr -> m { e with value = Array (Iarray.map map_expr arr) }
  | Prod l -> m { e with value = Prod (List.map map_expr l) }
  | Ext ext -> m { e with value = Ext (m_ext ext)}

  
let [@warning "-4"] expr_vars (ext_vars: 'ext -> (string * 't) list) : (string * 't) list -> ('ext,'t) expr -> (string * 't) list = fun x -> 
  fold_expr ext_vars (fun l e -> match e.value with Var (x, t) -> (x, t) :: l | _ -> l) x


type standard_logic_bop =  Equiv | Arrow | LAnd | LOr | Program of string
type standard_logic_uop = LNot


module type BoolA = sig
  include HardyMisc.Utils.PRETTY_TYPE
  include HardyMisc.Utils.FUNCTOR with type 'a t := 'a t

  type atom 
  
  val conj : 'a t -> 'a t -> 'a t

  val disj : 'a t -> 'a t -> 'a t

  val tt : 'a t

  val ff : 'a t

  val neg : 'a t -> 'a t

  val atomic : atom -> 'a t
end

module Unit = struct
  type t = unit
end

(* module UnitBoolA : BoolA = struct
    type 'a t = unit
    type atom = ()
    let tt = ()
    let ff = ()
    let disj () () = ()
    let conj () () = ()
    let neg () = ()
    let map _ () = ()
    let atomic _ = ()
    let pp _ _ _ = ()
end
 *)

type 'a bool_a =
  | BA_True : 'a bool_a
  | BA_False : 'a bool_a
  | BA_Atom  : 'a -> 'a bool_a
  | BA_And : 'a bool_a * 'a bool_a -> 'a bool_a
  | BA_Or : 'a bool_a * 'a bool_a -> 'a bool_a
  | BA_Not : 'a bool_a -> 'a bool_a

let rec pp_boola : type a. ( Format.formatter -> a -> unit) -> Format.formatter -> a bool_a -> unit =
  fun pp_atom fmt ->
  let open Format in 
  function
  | BA_True -> pp_print_string fmt "true"
  | BA_False -> pp_print_string fmt "false"
  | BA_Atom a -> pp_atom fmt a
  | BA_And (f1,f2) -> fprintf fmt "(%a & %a)" (pp_boola pp_atom) f1 (pp_boola pp_atom) f2
  | BA_Or (f1,f2) -> fprintf fmt "(%a || %a)" (pp_boola pp_atom) f1 (pp_boola pp_atom) f2
  | BA_Not f -> fprintf fmt "~(%a)" (pp_boola pp_atom) f


let rec map_formula fa = function
  | BA_True -> BA_True
  | BA_False -> BA_False
  | BA_Atom x -> BA_Atom (fa x)
  | BA_And (f1,f2) -> BA_And (map_formula fa f1,map_formula fa f2)
  | BA_Or (f1,f2) -> BA_Or (map_formula fa f1,map_formula fa f2)
  | BA_Not f -> BA_Not (map_formula fa f) 


let rec fold_formula j pj init form = match form with
  | BA_True | BA_False -> j form init
  | BA_Atom p -> pj p init
  | BA_And (f1,f2) | BA_Or (f1,f2) -> j form (fold_formula j pj (fold_formula j pj init f1) f2)
  | BA_Not f -> j form (fold_formula j pj init f)


let pp_paren_atomic_boola f fmt  = 
  let open Format in   
  function [] -> Format.pp_print_string fmt "" | [x] -> f fmt [x] | l -> fprintf fmt "(%a)" f l


let pp_cnf_boola f fmt (s: 'a cnf)  : unit =
let open Format in
  pp_print_list
  ~pp_sep:(fun fmt () -> fprintf fmt " ∧ ")
  (fun fmt {disjuncts} -> 
    pp_paren_atomic_boola 
    (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ∨ ") (fun fmt a -> f fmt a) )
      fmt disjuncts)
  fmt
  s.conjuncts



(* overkill to use fold here but a 'fun' example *)
let formula_depth f = 
  (* todo: some lazy monad *)
  let lazy_bind (x:'a Lazy.t) (f: 'a -> 'b Lazy.t) : 'b Lazy.t = Lazy.force_val x |> f in
  let open Lazy in
  let (let*) = lazy_bind in
  let (let+) x f = lazy_bind x (fun x -> f x |> from_val) in

  let [@warning "-4"] rec aux f = 
    fold_formula (fun f -> match f with 
    | BA_And (f1,f2) | BA_Or (f1,f2) ->  
      fun _ -> (* ignore delayed computation *)
      let* f1 = aux f1 in
      let+ f2 = aux f2 in 
      1 + Int.max f1 f2 
    | _ -> map ((+) 1)
    ) (fun _ -> map ((+) 1)) (from_val 0) f 
  in aux f |> force_val


(** 'a formula is a boolean algebra *)
(* module Formula : BoolA = struct
  type 'a t = 'a bool_a
  type atom = int
  let conj x y = And (x,y)
  let disj x y = Or (x,y)
  let tt = True
  let ff = False
  let neg x = Not x
  let map = map_formula
  let atomic x = Atom (x:int)
  let pp pp_atom = pp_boola pp_atom 
end *)

(* high-level program temporal specification *)
type ('temp_spec, 'spec_data, 'p) prog_with_spec = {prog_spec: ('temp_spec list,'spec_data) hoare_triple ; prog : 'p}


