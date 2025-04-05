(** {1 Misc Utilities} *)

type ('v, 'l) labeled = { value : 'v; label : 'l }

(** Token Location *)

type loc = Lexing.position * Lexing.position
type 'v locatable = ('v, loc option) labeled

let mk_labeled label value = { label; value }
let dummy_pos : loc = (Lexing.dummy_pos, Lexing.dummy_pos)
let mk_dummy_loc value = { value; label = None }

type 'f disjunction = { disjunct : 'f list }
(** type alias for list of disjunctive and conjunctive formulas *)

type 'f conjunction = { conjunct : 'f list }

(** [fold_mjoin f j init l] returns [init] if [l = nil], [f x] if [l] = [x] and
    otherwise, behaves like [List.fold_left] where the current value is applied
    to [f] before being applied with the accumulator to [j]. In the latter case,
    the initial value [init] is replaced by [j] applied to the first two
    elements.

    This function is useful to prevent extra terms in formulas: Instead of
    {m true \wedge x > 3}, we directly get {m x > 3}. *)
let fold_mjoin f j init = function
  | [] -> init
  | h :: [] -> f h
  | h1 :: h2 :: t ->
      List.fold_left (fun acc e -> j (f e) acc) (j (f h1) (f h2)) t

(** Infix function composition *)

let ( << ) f g x = f (g x)
let ( >> ) f g x = g (f x)

type (_, _, _, _) pair_app =
  | Left : ('a -> 'c) -> ('a, 'b, 'c, 'b) pair_app
  | Right : ('b -> 'd) -> ('a, 'b, 'a, 'd) pair_app
  | Both : ('a -> 'c) * ('b -> 'd) -> ('a, 'b, 'c, 'd) pair_app

(** function application to a pair *)
let pair_map (type i1 i2 o1 o2) (f : (i1, i2, o1, o2) pair_app)
    ((a, b) : i1 * i2) : o1 * o2 =
  match f with
  | Left f -> (f a, b)
  | Right f -> (a, f b)
  | Both (f1, f2) -> (f1 a, f2 b)

let add_opt_to_list (x : 'a option) (l : 'a list) : 'a list =
  Option.fold ~none:l ~some:(fun x -> x :: l) x
