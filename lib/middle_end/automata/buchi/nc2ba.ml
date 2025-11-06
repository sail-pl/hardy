(* open MiddleParser.SyntaxCommon *)
open MiddleParser.NcSyntax

module Vertex : Graph.Sig.COMPARABLE with type t = string = struct
  (* states are just labels *)
  type t = string

  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

(* output of ltl2ba with formula for each arc *)
module Arc : Graph.Sig.ORDERED_TYPE_DFT with type t = BoolA.disjunct_set = struct
  type t =   BoolA.disjunct_set

  let compare = Stdlib.compare
  let default : BoolA.disjunct_set =  BoolA.(mk_disjunct (DnfBASet.empty))
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
  BuchiSig.S with type E.label =  BoolA.disjunct_set and type init_val = neverclaim =
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
             BoolA.(tr.pml_form |> nnf_of_boola |> dnf_of_boola |> mk_disjunct)
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
  let string_of_edge (f : E.label) = Format.asprintf "%a"  (BoolA.pp_dnf_boola (fun fmt s -> Format.pp_print_string fmt (Atoms.get s |> fst))) f.boola_disjunct
  let get_vdata _ = ()

  let get_edge_type (e : E.label) =
    let open BuchiSig in
    match  BoolA.DnfBASet.cardinal e.boola_disjunct with 
    | 0 -> Universal 
    | 1 when  BoolA.(AtomicBASet.exists (function False -> true | _ -> false) (DnfBASet.choose e.boola_disjunct)) -> Blocking 
    | _ -> Unknown
end
