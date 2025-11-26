open SyntaxCommon

(** {1 Parse tree for Promela neverclaims} *)

type state = { pml_state : string }
type transition = { pml_src : state; pml_form : string eba; pml_dst : state }
type neverclaim = { pml_states : state list; pml_transitions : transition list }