open HardyFrontEnd
open Syntax
open Syntax.Fol
open Syntax.Program
open Syntax.Shared
open Syntax.Instant
open HardyMisc.Utils
open MiddleParser.NcSyntax
module Atom = Atom.Imperative ()
module B = Ba.Make (Atom)
module DotB = BuchiSig.Dot (B)
module BProd = BaProduct.Make (B) (Atom)
module BProdU = BuchiSig.Utils (BProd)
module DotBProd = BuchiSig.Dot (BProd)

(* type info = { i : int } *)

let fol_of_bform m = fol_of_bform (fun a -> m (Atom.get a |> snd))

(* create a map binding the exit-arc rely formula to all its guarantee ones *)
module M = Map.Make (struct
  type t = string bform * min_nb_instants

  let compare ((e1, _) : t) ((e2, _) : t) =
    String.compare (e1 |> string_of_bform Fun.id) (e2 |> string_of_bform Fun.id)
end)

let previous_instant_spec inputs in_e init_post =
  let inputs = List.map (pair_map (Right (fun t -> (Input, t)))) inputs in
  let replace_i (e : _ expr) =
    match e.value with
    | Var (v, inst) as var ->
        let value =
          match inst with
          | None when List.mem_assoc v inputs ->
              (* input is not the current instant input but the previous one*)
              Var (v, Some (Previous 1))
          | None ->
              (* state and output variables are for the current instant *)
              var
          | Some inst ->
              let inst =
                match inst with
                | Previous n ->
                    (* we are at the next instant, so previous values are 1 instant earlier *)
                    Previous (n + 1)
                | _ -> inst
              in
              Var (v, Some inst)
        in
        { e with value }
    | _ -> e
  in
  (* get the possible states to be in from the previous transition second component *)
  let requires =
    let l =
      List.map
        (fun e ->
          let l = BProd.E.label e in
          (* 'ensures' here are over history length + 1*)
          let nb_instant =
            add_nb_instant 1 BProd.(get_vdata (E.src e)).v_min_nb_instants
          in
          (l.arc_f.ensures, nb_instant))
        in_e
    in
    (* if an input led to no restriction on the state, then there is no need
               to put the other possible states.
               Indeed, if we prove the new state is independent of the current state,
               there is no need to check for others.
          *)
    if List.exists (fun f -> fst f = True) l then [] else l
  in
  (* todo: use env to type variables *)
  let requires =
    {
      disjunct =
        List.map
          (pair_map (Left (fol_of_bform (map_fol_pred (map_expr replace_i)))))
          requires;
    }
  in
  (* if this is an init_node, add the setup postcondition to the current triple precondition *)
  Option.fold init_post ~none:requires ~some:(fun cond ->
      {
        disjunct =
          (cond, { nb_instant = 0; is_max = true }) :: requires.disjunct;
      })

(** [generate_spec inputs in_e out_e init_post] builds the list of hoare pairs
    for a node of the product graph
    - [inputs : (string * ty) list] inputs of the program
    - [in_e : PG.edge list] entry arcs
    - [out_e : PG.edge list] exit arcs
    - [init_post] the initial formula if the node is a start node

    For each input formula occuring in exit arcs, computes \{(g_1 \/ ... \/ g_n)
    /\ <init_post> /\ f\} \{ g_1' \/ ... \/ g_m'\} where (., g_i') are in in_e
    and (f,g_i) are in out_e and init is there if defined. *)
let generate_spec (inputs : (string * base_ty) list)
    ((in_e, v, out_e) : BProd.edge list * BProd.vdata * BProd.edge list)
    (init_post : (_ expr, ty) fol option) :
    (ty, min_nb_instants) inst_spec_t disjunction conjunction hoare_pair list =
  assert (not (List.is_empty out_e));

  (* assert ((not (List.is_empty in_e)) || Option.is_some init_post); *)

  (* get the previous node ensures and adapt it to the current instant *)
  let previous_ens = previous_instant_spec inputs in_e init_post in

  (* if a variable from the current node precondition or postcondition refers to the instant n and we know we are at this instant, 
     remove the temporal quantification
     fixme: if nb_instant is >= n, should we create two new nodes, one where 
      it is reached for the first time (instant = n) and one where it is reached again (instant > n) ? 
    *)
  let at_current_instant_replace =
    if v.v_min_nb_instants.is_max = true then
      map_fol_pred
        (map_expr (fun e ->
             (* if a variable refers to the current instant, remove the instant quantification *)
             match e.value with
             | Var (x, Some (At n)) when n = v.v_min_nb_instants.nb_instant ->
                 { e with value = Var (x, None) }
             | _ -> e))
    else Fun.id
  in

  let fol_of_bform_replace =
    List.map (pair_map (Left (fol_of_bform at_current_instant_replace)))
  in

  let m =
    (* Factorize exit arcs by common first component by buildin a map from
       first components to matching second components *)
    List.fold_left
      (fun m e ->
        let l = BProd.E.label e in
        let prev_nb_instants = BProd.(get_vdata (E.src e)).v_min_nb_instants in
        M.add_to_list
          (l.arc_f.requires, prev_nb_instants)
          (* 'ensures' exit arcs are over the start of the next instant  *)
          (l.arc_f.ensures, Instant.add_nb_instant 1 prev_nb_instants)
          m)
      M.empty out_e
  in
  (* construct the spec for each first component *)
  M.fold
    (fun (req : string bform * min_nb_instants)
         (ens : (string bform * min_nb_instants) list)
         (s :
           (ty, min_nb_instants) inst_spec_t disjunction conjunction hoare_pair
           list) ->
      let requires : (ty, min_nb_instants) inst_spec_t disjunction conjunction =
        (*  predicate on possible states of current node, 
            every input and output variables refer to the begining and the end of the previous instant, respectively.    
         *)
        let current_req = { disjunct = fol_of_bform_replace [ req ] } in

        (* remove any trivial precondition *)
        let conjunct =
          List.filter
            (function
              | { disjunct = [ (f, _) ] } -> f.value <> FOL_True
              | { disjunct = [] } -> false
              | _ -> true)
            [ previous_ens; current_req ]
        in
        { conjunct }
      and ensures : (ty, min_nb_instants) inst_spec_t disjunction conjunction =
        (* disjunction of output properties sharing the same input property *)
        let disjunct =
          if List.exists (fun (f, _) -> f = True) ens then
            (* if one of them is true, nothing to ensure *)
            []
          else fol_of_bform_replace ens
        in
        { conjunct = [ { disjunct } ] }
      in
      if List.for_all (fun d -> List.is_empty d.disjunct) ensures.conjunct then
        (* discard when postcondition is true *) s
      else { requires; ensures } :: s)
    m []

let generate_triples (p : base_program) (a : BProd.t) :
    ( triple_data_t,
      (ty, min_nb_instants) inst_spec_t disjunction conjunction )
    hoare_triple
    list =
  let aux v =
    (* provide init post-condition for first node *)
    let extra_req =
      if BProd.is_start_node v then
        Option.(
          bind p.prog_setup (fun setup ->
              fold_mjoin some
                (fun x y -> bind (map and_fol y) (fun f -> map f x))
                None setup.setup_ensures))
      else None
    in

    let in_e = BProd.pred_e a v in
    let out_e = BProd.succ_e a v in

    let vdata = BProd.get_vdata v in

    let specs =
      generate_spec p.prog_decls.env_input (in_e, vdata, out_e) extra_req
    in

    (* if two or more transition share the same input, but with different outputs,
             we naively generate one spec per involved transition *)
    List.mapi
      (fun i s ->
        let open Format in
        let index = if i <> 0 then sprintf "_%i" i else "" in
        let id = BProd.(id_of_vertex v) ^ index in
        let data = { triple_id = id } in
        (data, s))
      specs
  in
  BProd.fold_vertex (aux >> List.append) a []
