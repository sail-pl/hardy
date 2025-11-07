type edge_type = Blocking | Universal | Unknown

module type S = sig
  include Graph.Sig.G

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

  module Atoms : Atom.S

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
      let vertex_name (v : vertex) = Format.asprintf "\"%a\"" pp_vertex v

      let edge_attributes e =
        let l = E.label e in
        [
          `Label (Format.asprintf "%a" pp_edge l);
          `Color
            (match get_edge_type l with
            | Universal -> 16762880
            | Blocking -> 16711680
            | Unknown -> 0);
        ]

      let vertex_attributes v =
        if acceptant v then [ `Shape `Doublecircle ] else []
    end)
  end
