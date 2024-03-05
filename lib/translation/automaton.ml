module AS = ArduinoSyntax.Automaton
module S = ArduinoSyntax.Syntax
open Graph

module Vertex : Sig.COMPARABLE with type t = string = struct
  (* states are just labels *)
  type t = string

  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

(* output of ltl2ba with formula for each arc *)
module Arc : Sig.ORDERED_TYPE_DFT with type t = AS.bform = struct
  type t = AS.bform

  let compare = Stdlib.compare
  let default = AS.True
end

(* to make the synchronised product of the rely and guarantee formula automaton,
   we need to remember when merging arcs which formula is the precondition and which is the postcondition *)
module PArc : Sig.ORDERED_TYPE_DFT with type t = AS.bform S.hoare_pair = struct
  type t = AS.bform S.hoare_pair

  let compare = Stdlib.compare
  let default = S.{ requires = AS.True; ensures = AS.True }
end

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

module Buchi (Atoms : TranslateUtils.AtomSig) :
  BuchiSig with type E.label = AS.bform and type init_val = AS.buchi_automaton =
struct
  include Imperative.Digraph.ConcreteLabeled (Vertex) (Arc)

  type init_val = AS.buchi_automaton

  let acceptant v = List.hd String.(split_on_char '_' v) = "accept"
  let is_start_node (v : V.t) = String.ends_with (V.label v) ~suffix:"init"

  let create ((states, arcs) : AS.buchi_automaton) : t =
    let g = create ~size:(List.length states) () in
    List.iter
      (fun (s1, f, s2) ->
        let e = E.create (V.create s1) f (V.create s2) in
        add_edge_e g e)
      arcs;
    g

  let string_of_vertex v =
    match String.split_on_char '_' v with
    | "accept" :: [ n ] -> n (* acceptant state *)
    | s :: [] -> s (* non-acceptant state *)
    | _ as x ->
        failwith (Printf.sprintf "bad label name : %s" (String.concat "" x))

  let id_of_vertex = string_of_vertex
  let string_of_edge (f : AS.bform) = AS.string_of_bform Atoms.subst f
end

(* synchronized product is of type G -> G -> PG *)

module BuchiProd
    (G : BuchiSig with type E.label = AS.bform)
    (Atoms : TranslateUtils.AtomSig) :
  BuchiSig with type init_val = G.t * G.t and type E.label = PArc.t = struct
  module MV =
    (* Util.DataV
       (struct type t = bool (* for marking treated states *) end) *)
      Util.CMPProduct (G.V) (G.V)
  (* /!\ make sure to always create vertices with the same argument order *)

  include Imperative.Digraph.ConcreteLabeled (MV) (PArc)

  type init_val = G.t * G.t

  let acceptant v =
    let l1, l2 = V.label v in
    G.acceptant l1 && G.acceptant l2

  let create (rely_a, guarantee_a) : t =
    let res = create ~size:G.(nb_vertex rely_a + nb_vertex guarantee_a) () in

    (* no vertex find function ?? *)
    let find_init_node g =
      G.fold_vertex
        (fun v acc ->
          match acc with
          | None -> if G.is_start_node v then Some v else None
          | v -> v)
        g None
      |> Option.get
    in

    (* the first node is made up of the first node from both automata *)
    let init_r, init_g = (find_init_node rely_a, find_init_node guarantee_a) in
    let init_node = V.create (init_r, init_g) in
    (* init queue with it *)
    let workq = Queue.create () in
    Queue.push init_node workq;

    while not (Queue.is_empty workq) do
      let curr_node = Queue.pop workq in

      let r, g = V.label curr_node in

      (* ... get all its out-transitions *)
      let r_out = G.succ_e rely_a r in
      let g_out = G.succ_e guarantee_a g in

      (* make the product of the destination node of the transitions *)
      List.iter
        (fun r ->
          List.iter
            (fun g ->
              let new_node = V.create G.(E.dst r, E.dst g) in
              (* add it to the list if not already treated *)
              if not (mem_vertex res new_node) then Queue.push new_node workq;
              (* make the curr_node -> new_node transition *)
              let label = S.{ requires = G.E.label r; ensures = G.E.label g } in
              let edge = E.create curr_node label new_node in
              add_edge_e res edge)
            g_out)
        r_out;
      ()
    done;
    res

  let is_start_node (v : V.t) =
    let l1, l2 = V.label v in
    G.is_start_node l1 && G.is_start_node l2

  let string_of_vertex v =
    let l1, l2 = V.label v in
    Format.sprintf "{pre_%s \n post_%s}"
      G.(string_of_vertex (V.label l1))
      G.(string_of_vertex (V.label l2))

  let id_of_vertex v =
    let l1, l2 = V.label v in
    Format.sprintf "pre_%s_post_%s"
      G.(string_of_vertex (V.label l1))
      G.(string_of_vertex (V.label l2))

  let string_of_edge (e : E.label) =
    Format.sprintf "requires: %s \n ensures : %s"
      (e.requires |> AS.string_of_bform Atoms.subst)
      (e.ensures |> AS.string_of_bform Atoms.subst)
end

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
