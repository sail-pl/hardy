(** {1 Parse tree for Promela neverclaims } *)

type bform = 
  | True
  | False
  | Atom of string
  | And of bform * bform
  | Or of bform * bform
  | Not of bform


type state = string

type transition = state * bform * state

type neverclaim = state list * transition list

let string_of_bform (convert_atom: string -> string)  = 
  let rec aux = function
  | True -> "true"
  | False -> "false"
  | Atom s -> convert_atom s
  | And (s1,s2) -> Format.sprintf "(%s) && (%s)" 
    (aux s1) 
    (aux s2)
  | Or (s1,s2) -> Format.sprintf "(%s) || (%s)" 
    (aux s1) 
    (aux s2)
  | Not s -> Format.sprintf "! (%s)" (aux s)
  in aux




