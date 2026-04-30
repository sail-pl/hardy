open HardyMisc.Utils

type base_ty = Ty_Int | Ty_Real | Ty_Bool | Ty_String | Ty_Array of base_ty * int option | Ty_Prod of base_ty list
type cat_ty = State | Input | Output | Local
type ty = cat_ty * (base_ty option)

let is_state (c,_ : ty) : bool = c = State
let is_input (c,_ : ty) : bool = c = Input
let is_output (c,_ : ty) : bool = c = Output


(** Standard Logic Operators *)

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
  | True : 'a bool_a
  | False : 'a bool_a
  | Atom  : 'a -> 'a bool_a
  | And : 'a bool_a * 'a bool_a -> 'a bool_a
  | Or : 'a bool_a * 'a bool_a -> 'a bool_a
  | Not : 'a bool_a -> 'a bool_a

let rec pp_boola : type a. ( Format.formatter -> a -> unit) -> Format.formatter -> a bool_a -> unit =
  fun pp_atom fmt ->
  let open Format in 
  function
  | True -> pp_print_string fmt "true"
  | False -> pp_print_string fmt "false"
  | Atom a -> pp_atom fmt a
  | And (f1,f2) -> fprintf fmt "(%a & %a)" (pp_boola pp_atom) f1 (pp_boola pp_atom) f2
  | Or (f1,f2) -> fprintf fmt "(%a || %a)" (pp_boola pp_atom) f1 (pp_boola pp_atom) f2
  | Not f -> fprintf fmt "~(%a)" (pp_boola pp_atom) f


let rec map_formula fa = function
  | True -> True
  | False -> False
  | Atom x -> Atom (fa x)
  | And (f1,f2) -> And (map_formula fa f1,map_formula fa f2)
  | Or (f1,f2) -> Or (map_formula fa f1,map_formula fa f2)
  | Not f -> Not (map_formula fa f) 


let rec fold_formula j pj init form = match form with
  | True | False -> j form init
  | Atom p -> pj p init
  | And (f1,f2) | Or (f1,f2) -> j form (fold_formula j pj (fold_formula j pj init f1) f2)
  | Not f -> j form (fold_formula j pj init f)


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
    | And (f1,f2) | Or (f1,f2) ->  
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

