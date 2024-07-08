(** {1 Misc Utilities} *)

(** Token Location *)

type loc = Lexing.position * Lexing.position
type 'v locatable = { loc : loc option; value : 'v }

let dummy_pos : loc = (Lexing.dummy_pos, Lexing.dummy_pos)
let mk_locatable loc value = { loc; value }
let mk_dummy_loc value = { value; loc = None }

(** [fold_mjoin f j init l] behaves like [List.fold_left f init l], when
    [List.length l < 2]. Otherwise, the join function [j] is used to combine the
    last two values. Particularly, the initial value [init] is replaced by [j]
    applied to the first two elements.

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

(* pairs *)

let pair_lmap f (a, b) = (f a, b)
let pair_rmap f (a, b) = (a, f b)
