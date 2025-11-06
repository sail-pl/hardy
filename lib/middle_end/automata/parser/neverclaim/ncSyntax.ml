open SyntaxCommon

(** {1 Parse tree for Promela neverclaims} *)

module BAAtom : BAAtomSig with type t = string = struct
  type t = string
  let to_string = Fun.id
end


module BoolA = BoolAlgebra(BAAtom)

type state = { pml_state : string }
type transition = { pml_src : state; pml_form : BoolA.t; pml_dst : state }
type neverclaim = { pml_states : state list; pml_transitions : transition list }