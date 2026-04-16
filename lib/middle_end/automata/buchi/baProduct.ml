open HardyFrontEnd
open Syntax.Program
(* open Syntax.Shared *)
open Syntax.Instant
(* open MiddleParser.SyntaxCommon *)


type 'a arc_data = {
    arc_f : 'a hoare_pair;
        (* length of the shortest path to each edge of the graph from the initial node *)
        (* mutable arc_min_nb_instants : min_nb_instants; *)
        (* true if there is only one possible path from the source vertex.
      this means 
      *)
  }

type vertex_data = { v_min_nb_instants : min_nb_instants }

(* warning: this module is statefull! *)
module Make(G : BuchiSig.S)
    :
  BuchiSig.S
    with type init_val = G.t * G.t
     and type E.label =  G.E.label arc_data
     and type vdata = vertex_data 
    = struct
      
  (* /!\ make sure to always create vertices with the same argument order *)


  (* Atoms not needed in the product *)
  module FAtom : Atom.S = struct 
    type _ t = unit 
    type atom = unit
    type data = unit 
    let subst _ = ()
    let register_atom _ = ()
    let get_atom_ids _ = ()
    let get_atom _ = ()
    let set_data _  _ = ()
    let get_data _ = ()
    let map _ _ = ()
    let join _ = ()
  end 
  module TAtom : MiddleParser.Labeling.TseitinAtomSig = struct 
    type t = unit 
    let neg _ = ()
    let create _ = ()
    let pp _ _ = () 
    let fresh () = ()
    let get_atom_id _ = ""
    let is_neg _ = false
    let is_generated _ = false
  end 
  
  (* module BA = BoolAlgebra(TAtom) *)

 module Transition : Graph.Sig.ORDERED_TYPE_DFT with type t =  G.E.label arc_data = struct
    type t =  G.E.label arc_data

    let compare = Stdlib.compare

    let default : t =
      {
        arc_f = { requires = G.Transition.default ; ensures = G.Transition.default};
        (* arc_min_nb_instants = { nb_instant = 0; is_max = false }; *)
      }
  end

  (* returned graph *)
  module GProd =
    Graph.Imperative.Digraph.ConcreteLabeled
      (Graph.Util.CMPProduct (G.V) (G.V)) (Transition)

  include GProd

  type vdata = vertex_data

  module H = Hashtbl.Make (V)

  let vertices : vdata H.t = H.create 50
  let get_vdata = H.find vertices
  let set_vdata = H.replace vertices

  type init_val = G.t * G.t

  let is_start_node (v : V.t) =
    let l1, l2 = V.label v in
    G.is_start_node l1 && G.is_start_node l2

  let [@warning "-4"] get_edge_type (e : E.label) =
    let req = G.get_edge_type e.arc_f.requires
    and ens = G.get_edge_type e.arc_f.ensures in
    match (req, ens) with
    | Universal, Universal -> BuchiSig.Universal
    | _, Blocking -> Blocking
    | _ -> Unknown

  let pp_vertex fmt v =
    let l1, l2 = V.label v in
    Format.fprintf fmt "{pre_%a @, post_%a} @. insts %s %i"
      G.pp_vertex l1
      G.pp_vertex l2
      (if (get_vdata v).v_min_nb_instants.is_max then "=" else "≥")
      (get_vdata v).v_min_nb_instants.nb_instant

  let id_of_vertex v =
    let l1, l2 = V.label v in
    Format.asprintf "pre_%a_post_%a"
      G.pp_vertex l1
      G.pp_vertex l2

  let pp_edge fmt (e : E.label) = 
    match (e.arc_f.requires, e.arc_f.ensures) with
    (* | True, True -> "Σ" (* universal edge *)
    | True, _ -> Format.sprintf "ensures: %s @," e_s
    | _, True -> Format.sprintf "requires: %s @," r_s *)
    | _ -> Format.fprintf fmt "requires: %a @, ensures : %a" 
        G.pp_edge e.arc_f.requires 
        G.pp_edge e.arc_f.ensures

  let acceptant (v : vertex) : bool =
    let l1, l2 = V.label v in
    G.acceptant l1 && G.acceptant l2

  let refine_length init_node (a : t) : unit =
    let module Bfs = Graph.Traverse.Bfs (GProd) in
    Bfs.iter_component
      (fun v ->
        let vdata = get_vdata v in
        let preds = pred a v in
        let get_min_nb_instants v = (get_vdata v).v_min_nb_instants in
        (* we already have the lowest possible number of instant, we just need to know if it is the exact length *)
        let is_max =
          (join_nb_instant (List.map get_min_nb_instants preds)).is_max
        in
        set_vdata v
          { v_min_nb_instants = { vdata.v_min_nb_instants with is_max } })
      a init_node

  (** Given two Buchi automata A and B, [create A B] returns a Buchi automaton C
      that is the synchronous parallel composition of A and B. Thus, a word is
      recognized by C iff it is recognized by both A and B. We make sure to keep
      the labels and remember their origin as it is crucial for our purposes

      fixme: correctly implement to support liveness (see my notes) *)
  let create (rely_a, guarantee_a) : t =  

    let product_g =
      create ~size:G.(nb_vertex rely_a + nb_vertex guarantee_a) ()
    in

    let add_node n d =
      add_vertex product_g n;
      H.replace vertices n d
    in

    (* the first node is made up of the first node from both automata *)

    (* we assume there is only one init node *)
    let init_r, init_g =
      let open BuchiSig.Utils (G) in
      match (get_all_init_nodes rely_a, get_all_init_nodes guarantee_a) with
      | h1 :: [], h2 :: [] -> (h1, h2)
      | _ -> failwith "no or more than one initial state"
    in

    let init_h_length = { nb_instant = 0; is_max = false } in

    let init_node = (init_r, init_g) in

    add_node init_node { v_min_nb_instants = init_h_length };

    (* init queue with it *)
    let workq = Queue.create () in
    Queue.push init_node workq;

    while not (Queue.is_empty workq) do
      let curr_node = Queue.pop workq in

      let r, g = V.label curr_node in

      let curr_node_data = get_vdata curr_node in

      (* the new node is at the next instant *)
      let v_min_nb_instants =
        add_nb_instant 1 curr_node_data.v_min_nb_instants
      in

      let next_node_data = { v_min_nb_instants } in

      let [@warning "-4"] create_edge (r, g) =
        let next_node = G.(E.dst r, E.dst g) in
        (* add it to the list if not already treated 
        (mem_vertex will only check the label, not the vertex data, which is precisely what we want
          as any previous entry will have a smaller minimum instant due to the BFS )
        *)
        if not (mem_vertex product_g next_node) then (
          Queue.push next_node workq;
          add_node next_node next_node_data);
        (* make the curr_node -> new_node transition *)
        let arc_f = { requires = G.E.label r; ensures = G.E.label g } in
        let edge =
          E.create curr_node
            {
              arc_f;
              (* arc_min_nb_instants = curr_node_data.v_min_nb_instants *)
            }
            next_node
        in
        (match get_edge_type (E.label edge) with
        | Universal ->
            (* Format.printf
              "warning: product automaton contains a universal edge between \
               node '%s' and '%s' \n"
              (id_of_vertex curr_node) (id_of_vertex next_node) *)
            ()
        | Blocking ->
            (* Format.printf
              "warning: product automaton contains a blocking edge between \
               node '%s' and '%s' \n"
              (id_of_vertex curr_node) (id_of_vertex next_node) *)
            ()
        | _ -> ());
        add_edge_e product_g edge
      in

      (* make the product of the destination node of the transitions *)
      G.iter_succ_e
        (fun r -> G.iter_succ_e (fun g -> create_edge (r, g)) guarantee_a g)
        rely_a r
    done;
    refine_length init_node product_g;
    product_g
end
