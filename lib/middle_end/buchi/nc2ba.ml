open MiddleParser.NcSyntax

module Vertex : Graph.Sig.COMPARABLE with type t = string = struct
  (* states are just labels *)
  type t = string

  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

(* output of ltl2ba with formula for each arc *)
module Arc : Graph.Sig.ORDERED_TYPE_DFT with type t = string bform = struct
  type t = string bform

  let compare = Stdlib.compare
  let default = True
end

module Utils (G : Graph.Sig.I) = struct
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

module Make (Atoms : Atom.S with type 'a t = 'a) :
  BuchiSig.S with type E.label = string bform and type init_val = neverclaim =
struct
  include Graph.Imperative.Digraph.ConcreteLabeled (Vertex) (Arc)

  type init_val = neverclaim
  type vdata = unit

  let acceptant v = List.hd String.(split_on_char '_' v) = "accept"
  let is_start_node (v : V.t) = String.ends_with (V.label v) ~suffix:"init"

  let create (claim : neverclaim) : t =
    let g = create ~size:(List.length claim.pml_states) () in
    List.iter
      (fun tr ->
        let e =
          E.create
            (V.create tr.pml_src.pml_state)
            tr.pml_form
            (V.create tr.pml_dst.pml_state)
        in
        add_edge_e g e)
      claim.pml_transitions;
    g

  let string_of_vertex v =
    match String.split_on_char '_' v with
    | "accept" :: [ n ] -> n (* acceptant state *)
    | s :: [] -> s (* non-acceptant state *)
    | _ -> v (* others *)

  let id_of_vertex = string_of_vertex
  let string_of_edge (f : string bform) = string_of_bform Atoms.subst f
  let get_vdata _ = ()

  let get_edge_type (e : E.label) =
    let open BuchiSig in
    match e with True -> Universal | False -> Blocking | _ -> Unknown
end
