open HardyFrontEnd.Syntax.Shared

(** {1 Parse tree for Promela neverclaims} *)

type state = { pml_state : string }
type transition = { pml_src : state; pml_form : string bool_a; pml_dst : state }
type neverclaim = { pml_states : state list; pml_transitions : transition list }