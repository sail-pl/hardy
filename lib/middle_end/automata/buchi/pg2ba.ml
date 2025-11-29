open HardyFrontEnd.Syntax
open Program
open MiddleParser.SyntaxCommon
open HardyFrontEnd.Printer

module Vertex : Graph.Sig.COMPARABLE with type t = string = struct
  (* states are just labels *)
  type t = string

  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

(* output of ltl2ba with formula for each arc *)
module Arc : Graph.Sig.ORDERED_TYPE_DFT with type t = unit expr option = struct
  type t = unit expr option

  let compare = Stdlib.compare
  let default = None
end

module M :
  BuchiSig.S
    with type E.label = unit expr option
     and type init_val = (Shared.ty fol_t, unit) node list = struct
  include Graph.Imperative.Digraph.ConcreteLabeled (Vertex) (Arc)

  module TAtom = EmptyTAtom
  module FAtom = Atom.Empty
  module BA = BoolAlgebra(TAtom)

  module Transition = struct
    type t = unit expr option

    let compare = Stdlib.compare
    let default : t =  None
  end

  type init_val = (Shared.ty fol_t, unit) node list
  type vdata = unit

  let acceptant _ = false
  let is_start_node (v : V.t) = v = "START"

  let create (p : _ node list) : t =
    let g = create ~size:(List.length p) () in
    List.iter
      (fun node ->
        List.iter
          (fun (guard, _, next) ->
            let succ = Option.value next ~default:node.node_id in
            let e = E.create (V.create node.node_id) guard (V.create succ) in
            add_edge_e g e)
          node.node_transitions)
      p;
    g

  let pp_vertex fmt v = Format.fprintf fmt "%s" v
  let id_of_vertex = Fun.id

  let pp_edge fmt (e : _ expr option) =
    Format.(
      fprintf fmt "%a"
        (pp_print_option (pp_exp (fun fmt (v, _) -> fprintf fmt "%s" v)))
        e)

  let get_vdata _ = ()

  let get_edge_type (e : E.label) =
    let open BuchiSig in
    match e with Some _ -> Unknown | None -> Universal
end