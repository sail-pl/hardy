open HoaSyntax

exception Missing_item of string

val get_props : hoa -> string list

val get_acceptance : hoa -> (int * accept_cond )

val get_atoms : hoa -> (int * string) list

val get_start : hoa -> int list

val get_num_states : hoa -> int option