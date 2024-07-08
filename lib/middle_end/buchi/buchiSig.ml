module type S = sig
  include Graph.Sig.G

  type init_val

  val create : init_val -> t
  val is_start_node : V.t -> bool
  val acceptant : V.t -> bool
  val string_of_vertex : V.t -> string
  val id_of_vertex : V.t -> string
  val string_of_edge : E.label -> string
end

(** Buchi-specific graph utilities *)
module type UtilsSig = functor (G : S) -> sig
  val get_all_init_nodes : G.t -> G.vertex list
end

(** Generation of dot file *)
module type DotSig = functor (G : S) -> sig
  val fprint_graph : Format.formatter -> G.t -> unit
  val output_graph : out_channel -> G.t -> unit
end

module Utils : UtilsSig =
functor
  (G : S)
  ->
  struct
    (* no vertex find function ?? *)
    let get_all_init_nodes g =
      G.fold_vertex
        (fun v acc -> if G.is_start_node v then v :: acc else acc)
        g []
  end

module Dot : DotSig =
functor
  (G : S)
  ->
  struct
    include Graph.Graphviz.Dot (struct
      include G

      let default_vertex_attributes _ =
        [ `Shape `Circle; `Fixedsize true; `Height 0.8; `Fontsize 10 ]

      let default_edge_attributes _ = [ `Fontsize 10 ]
      let get_subgraph _ = None
      let graph_attributes _g = []
      let vertex_name (v : vertex) = "\"" ^ string_of_vertex v ^ "\""
      let edge_attributes e = [ `Label (E.label e |> string_of_edge) ]

      let vertex_attributes v =
        if acceptant v then [ `Shape `Doublecircle ] else []
    end)
  end
