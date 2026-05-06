type edge_type = Blocking | Universal | Unknown

module VertexFind : (G : Graph.Sig.I) ->
sig
    exception Found of G.vertex
    val find_v_opt : G.t -> G.V.label -> G.vertex option
end

module type S = sig
    include Graph.Sig.G


    module Transition : Graph.Sig.ORDERED_TYPE_DFT with type t := E.label

    type init_val
    type vdata

    val create : init_val -> t
    val is_start_node : V.t -> bool
    val acceptant : V.t -> bool
    val pp_vertex : Format.formatter -> V.t -> unit
    val id_of_vertex : V.t -> string
    val pp_edge : Format.formatter -> E.label -> unit
    val get_edge_type : E.label -> edge_type
    val get_vdata : V.t -> vdata
end

(** Buchi-specific graph utilities *)
module Utils(G:S) : sig
    val get_all_init_states : G.t -> G.vertex list 
    
    val get_nonacc_states : G.t -> G.V.t list list
    (** [get_nonacc_states g] returns the list of non-acceptant cicles, that is, 
        if this list is not empty and the automaton is complete and deterministic, it is not a safety automaton because there exists a loop that only consists of non-accepting states,
        so that can produce an infinite word not part of the language
    *)
end

(** Generation of dot file *)
module Dot(G:S) : sig
    val fprint_graph : Format.formatter -> G.t -> unit
    val output_graph : out_channel -> G.t -> unit
end
