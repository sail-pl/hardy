type edge_type = Blocking | Universal | Unknown


module VertexFind (G : Graph.Sig.I) = struct
  (* no vertex find function ??
    -> from the manual: 
    "you should better keep the vertices as long as you create them."
  *)
  exception Found of G.V.t

  let find_v_opt g i =
    try
      G.iter_vertex (fun v -> if G.V.label v = i then raise (Found v)) g;
      None
    with Found v -> Some v
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




module Utils =
functor
  (G : S)
  ->
  struct

  open HardyMisc.Utils

    let get_all_init_states g =
      G.fold_vertex
        (fun v acc -> if G.is_start_node v then v :: acc else acc)
        g []
  

    (*
      two possibilities :
      - current node is acceptant -> skip
      - there exists a successor that is non-acceptant ->
         recurse until we loop back to the current node via a path of non-accepting-paths
    *)
    let get_nonacc_states g = 
      let rec aux first = function
      | [] ->  
        check (G.succ g first |> List.filter (G.acceptant >> not)) first []
      | h::t as path -> 
        if List.mem h t then path
        else
          check (G.succ g h |> List.filter (G.acceptant >> not)) first path
          
      and check succs first path =          
        List.fold_left (fun acc s -> 
          if acc <> [] then
            (* we found it, skip *)
            acc
          else
            aux first (s::path)
        ) [] succs
  
      in
    
      G.fold_vertex (fun v acc -> 
        if acc <> [] then (* skip *)  acc else
        match aux v [] with [] -> acc | l -> l::acc
      ) 
    g []

  end

module Dot =
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
        []
        |> fun x -> if acceptant v then List.cons (`Shape `Doublecircle) x else x
        |> fun x -> if is_start_node v then List.cons (`Style `Filled ) x else x
    end)
  end