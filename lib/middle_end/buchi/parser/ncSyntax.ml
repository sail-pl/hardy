open HardyFrontEnd.Syntax.Fol
open HardyMisc.Utils

(** {1 Parse tree for Promela neverclaims} *)

type 'a bform =
  | True
  | False
  | Atom of 'a
  | And of 'a bform * 'a bform
  | Or of 'a bform * 'a bform
  | Not of 'a bform

let ( <-> ) f1 f2 = And (Or (Not f1, f2), Or (Not f2, f1))
let ( --> ) f1 f2 = Or (Not f1, f2)

type state = { pml_state : string }
type transition = { pml_src : state; pml_form : string bform; pml_dst : state }
type neverclaim = { pml_states : state list; pml_transitions : transition list }

let rec map_bform_atom : type a b. (a -> b) -> a bform -> b bform =
 fun m -> function
  | Atom a -> Atom (m a)
  | And (b1, b2) -> And (map_bform_atom m b1, map_bform_atom m b2)
  | Or (b1, b2) -> Or (map_bform_atom m b1, map_bform_atom m b2)
  | Not b -> Not (map_bform_atom m b)
  | (True | False) as x -> x

let string_of_bform (convert_atom : string -> string) =
  let rec aux = function
    | True -> "true"
    | False -> "false"
    | Atom s -> convert_atom s
    | And (s1, s2) -> Format.sprintf "(%s) && (%s)" (aux s1) (aux s2)
    | Or (s1, s2) -> Format.sprintf "(%s) || (%s)" (aux s1) (aux s2)
    | Not s -> Format.sprintf "! (%s)" (aux s)
  in
  aux

let fol_of_bform (convert_atom : 'a -> 'b fol) : 'a bform -> 'b fol =
  let rec aux : 'a bform -> 'b fol = function
    | True -> mk_dummy_loc FOL_True
    | False -> mk_dummy_loc FOL_False
    | Atom s -> convert_atom s
    | And (s1, s2) ->
        let s1 = aux s1 in
        let s2 = aux s2 in
        mk_dummy_loc (FOL_Binary (s1, And, s2))
    | Or (s1, s2) ->
        let s1 = aux s1 in
        let s2 = aux s2 in
        mk_dummy_loc (FOL_Binary (s1, Or, s2))
    | Not s ->
        let s = aux s in
        mk_dummy_loc (FOL_Unary (Not, s))
  in
  aux
