module type SIMP_TYPE = sig
  type t
end

module type TYPE = sig
  type 'a t
end


module type PRETTY_SIMP_TYPE = sig
  include SIMP_TYPE
  val pp : Format.formatter -> t -> unit
end


module type PRETTY_TYPE = sig
  include TYPE
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end


module type FUNCTOR = sig
  include TYPE

  val map : ('a -> 'b) -> 'a t -> 'b t
end

module type MONADIC = sig
  include FUNCTOR
    val join : 'a t t -> 'a t
end

type ('v, 'l) labeled = { value : 'v; label : 'l }


type loc = Lexing.position * Lexing.position
type 'v locatable = ('v, loc option) labeled

let mk_labeled ~label value = { label; value }
let map_value f lv = {lv with value=f lv.value}
let map_label f lv = {lv with label=f lv.label}

(* 
  cannot write generic map: if the function is not present, it must use the previous value, which is of type 'a. 
  So, if the function is present, it can only create value of type 'a from 'a

let map_labeled (type a b) ?m_value:(mv_opt: (a -> b) option) ?m_label:ml_opt lv = 
  let label = Option.fold ~none:lv.label ~some:(fun f -> f lv.label) ml_opt
  and value = Option.fold ~none:lv.value ~some:(fun f -> f lv.value) mv_opt in 
  {value;label} 

let map_value f = fun x -> map_labeled ~m_value:f x
let map_label f = fun x -> map_labeled ~m_label:f x
*)

let dummy_pos : loc = (Lexing.dummy_pos, Lexing.dummy_pos)
let mk_dummy_loc value = { value; label = None }


type 'f disjunction = { disjuncts : 'f list }
let mk_disj disjuncts = { disjuncts }
let disj_singleton x = { disjuncts=[x]}
let map_disjuncts f d = {disjuncts=List.map f d.disjuncts}
let add_disjunct d l = {disjuncts=d::l.disjuncts}
let append_disjuncts c1 c2 = {disjuncts=List.append c1.disjuncts c2.disjuncts}
let disj_empty = { disjuncts=[]}


type 'f conjunction = { conjuncts : 'f list}
let mk_conj conjuncts = { conjuncts }
let map_conjuncts f d = {conjuncts=List.map f d.conjuncts }
let conj_singleton x = { conjuncts=[x]}
let conj_empty = { conjuncts=[]}
let add_conjunct d l = {conjuncts=d::l.conjuncts}
let append_conjuncts c1 c2 = {conjuncts=List.append c1.conjuncts c2.conjuncts}


type 'a cnf = 'a disjunction conjunction

let fold_mjoin f j init = function
  | [] -> init
  | h :: [] -> f h
  | h1 :: h2 :: t ->
      List.fold_left (fun acc e -> j (f e) acc) (j (f h1) (f h2)) t


let ( << ) f g x = f (g x)
let ( >> ) f g x = g (f x)

type (_, _, _, _) pair_app =
  | Left : ('a -> 'c) -> ('a, 'b, 'c, 'b) pair_app
  | Right : ('b -> 'd) -> ('a, 'b, 'a, 'd) pair_app
  | Both : ('a -> 'c) * ('b -> 'd) -> ('a, 'b, 'c, 'd) pair_app

let pair_map (type i1 i2 o1 o2) (f : (i1, i2, o1, o2) pair_app)
    ((a, b) : i1 * i2) : o1 * o2 =
  match f with
  | Left f -> (f a, b)
  | Right f -> (a, f b)
  | Both (f1, f2) -> (f1 a, f2 b)

let add_opt_to_list (x : 'a option) (l : 'a list) : 'a list =
  Option.fold ~none:l ~some:(fun x -> x :: l) x

module Bindings = Map.Make(String)
