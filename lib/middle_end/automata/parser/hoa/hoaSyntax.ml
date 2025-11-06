(* open HardyFrontEnd.Syntax.Fol
open HardyMisc.Utils *)

(** {1 Parse tree for the Hanoi Omega-Automata Format (HOA) } *)

type any = AnyBool of bool | AnyInt of int | AnyString of string | AnyId of string

type label_expr = 
  | BoolLabel of bool 
  | IntLabel of int (* atomic prop number*)
  | NameLabel of string (* previously defined alias *)
  | ConjLabel of label_expr * label_expr
  | DisjLabel of label_expr * label_expr
  | NotLabel of label_expr

type accept_cond = 
  | SetCond of {fin_occur: bool ; set_number: int ; complement:bool}
  | BoolAccept of bool
  | ConjAccept of accept_cond * accept_cond
  | DisjAccept of accept_cond * accept_cond

type header_item = 
  (* number of automaton states*)
  | States of int 
  (* initial states, singleton if the automaton is non-alternating  *)
  | Start of int list
  (* number of atomic propositions followed by unique names for them (implicitely numbered from left to right, starting from 0 ) *)
  | Atomic of int * string list
  (* name for atomic propositions, or common subformulas used as labels for conciseness *)
  | Alias of string * label_expr 
  (* number of acceptance sets numbered from 0 to n-1 *)
  | Accept of int * accept_cond
  (* name of the acceptance condition and its parameters (either a string or an int) *)
  | AcceptName of string * ((string,int) Either.t list)
  (* tool used to produce the automaton and its version *)
  | Tool of string * string option
  (* name of the automaton *)
  | Name of string
  (* properties of the automaton, eg. deterministic *)
  | Properties of string list
  (* Non-standard properties *)
  | Other of any list


(**
  - items must always contain one [Accept] item
  - items can contains multiple instances of [Start], [Alias] and [Properties], but not anything else
  - [Other] items begining with a lowercase can be ignored (do not change the automaton semantics )
  - [Other] items begining with an uppercase and not supported must at least trigger a warning (affect the automaton semantics)
*)
type header = {
  version : string ;
  items : header_item list ;
}

type state = {
    state_number : int;
    state_label : label_expr option ;
    state_name : string option;
    state_acc_sets : int list
}


type edge = {
  (* non-alternating automata can only use the OneState constructor of state_conj *)
  edge_dst : int list ; (* singleton if the automaton is non-alternating  *)
  edge_label : label_expr option ;
  edge_acc_sets : int list
} 

type body = (state * (edge list)) list


type hoa = {header: header ; body : body}

