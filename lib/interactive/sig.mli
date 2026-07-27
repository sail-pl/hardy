(** front-end<->middle-end<->back-end *)

module type S = sig
  (* type automaton
  type node *)
  type program
  type proof_result = Success | Failure of string

  (* type query_result *)
  type proof_state
  type backend_state
  type vc

  (** a triple must uniquely identify how it was constructed from the automaton: node_id + in transition id + out transition id  
    -> each formula is annoted
    -> possibility to display the triple to tell what to do
  *)
  type triples

  (** prepare the environnement from the program declarations and setup procedure *)
  val init_backend : program -> backend_state
  val get_vcs : backend_state -> triples -> vc list

  (** get the verification condition identifier *)
  val get_vc_id : vc -> string

  (** attempt to prove the given triples, returning for each triple if it was proved or not  
      -> failed triples are reported to the user 
    
  *)
  val prove : backend_state -> vc -> proof_result

  (* when a query triggers a recomputation of the automaton, it must communicate what triples are obsolete, new, or changed *)
  (* make a query on the automaton:
    - get all triples
    - get a specific triple
    - delete an out transition
  *)

  (* val get_init_node : automaton -> node
  (* val get_node_triples : program -> automaton -> node -> triple list *)
  val get_next_node : automaton -> triple -> node
  val node_eq : node -> node -> bool
  val triple_eq : triple -> triple -> bool
  val triple_hash : triple -> int *)


  (* val query_automaton : automaton -> query -> query_result *)

  (* generate the whyml file for manual proving (later: proof certificate) *)
  (* val write_program : program -> triple list -> unit *)
  (* val get_user_query : proof_state -> query *)
end
