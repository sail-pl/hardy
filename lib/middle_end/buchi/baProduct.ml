open HardyFrontEnd.Syntax.Program
open MiddleParser.NcSyntax

module Arc : Graph.Sig.ORDERED_TYPE_DFT with type t = string bform hoare_pair =
struct
  type t = string bform hoare_pair

  let compare = Stdlib.compare
  let default = { requires = True; ensures = True }
end

module Make
    (G : BuchiSig.S with type E.label = string bform)
    (Atoms : Atom.S with type 'a t = 'a) :
  BuchiSig.S with type init_val = G.t * G.t and type E.label = Arc.t = struct
  module MV =
    (* Util.DataV
       (struct type t = bool (* for marking treated states *) end) *)
      Graph.Util.CMPProduct (G.V) (G.V)
  (* /!\ make sure to always create vertices with the same argument order *)

  include Graph.Imperative.Digraph.ConcreteLabeled (MV) (Arc)
  open BuchiSig.Utils (G)

  type init_val = G.t * G.t

  let acceptant v =
    let l1, l2 = V.label v in
    G.acceptant l1 && G.acceptant l2

  (** Given two Buchi automata A and B, [create A B] returns a Buchi automaton C
      that is the synchronous parallel composition of A and B. Thus, a word is
      recognized by C iff it is recognized by both A and B. We make sure to keep
      the labels and remember their origin as it is crucial for our purposes

      fixme: correctly implement to support liveness (see my notes) *)
  let create (rely_a, guarantee_a) : t =
    let res = create ~size:G.(nb_vertex rely_a + nb_vertex guarantee_a) () in

    (* the first node is made up of the first node from both automata *)

    (* we assume there is only one init node *)
    let init_r, init_g =
      match (get_all_init_nodes rely_a, get_all_init_nodes guarantee_a) with
      | h1 :: [], h2 :: [] -> (h1, h2)
      | _ -> failwith "no or more than one initial state"
    in
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
              let label = { requires = G.E.label r; ensures = G.E.label g } in
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
    Format.sprintf "{pre_%s @, post_%s}"
      G.(string_of_vertex l1)
      G.(string_of_vertex l2)

  let id_of_vertex v =
    let l1, l2 = V.label v in
    Format.sprintf "pre_%s_post_%s"
      G.(string_of_vertex l1)
      G.(string_of_vertex l2)

  let string_of_edge (e : E.label) =
    Format.sprintf "requires: %s @, ensures : %s"
      (e.requires |> string_of_bform Atoms.subst)
      (e.ensures |> string_of_bform Atoms.subst)
end
