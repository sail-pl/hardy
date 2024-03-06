(** Synopsis *)
(** {0 Buchi automata } *)

open Graph

(** {3 Signature for Büchi automata } *)

module type BuchiSig = sig
  include Graph.Sig.G

  type init_val

  val create : init_val -> t
  val is_start_node : V.t -> bool
  val acceptant : V.t -> bool
  val string_of_vertex : V.label -> string
  val id_of_vertex : V.label -> string
  val string_of_edge : E.label -> string
end

(** {3 Generation of dot file }*)

module BuchiDot (G : BuchiSig) = struct
  include Graphviz.Dot (struct
    include G

    let default_vertex_attributes _ =
      [ `Shape `Circle; `Fixedsize true; `Height 0.8; `Fontsize 10 ]

    let default_edge_attributes _ = [ `Fontsize 10 ]
    let get_subgraph _ = None
    let graph_attributes _g = []
    let vertex_name (v : vertex) = "\"" ^ string_of_vertex (V.label v) ^ "\""
    let edge_attributes e = [ `Label (E.label e |> string_of_edge) ]

    let vertex_attributes v =
      if acceptant v then [ `Shape `Doublecircle ] else []
  end)
end

