open HardyFrontEnd
open FrontSig
open Syntax
open Syntax.Fol
open Syntax.Shared
open Syntax.Instant
open HardyMisc.Utils
open Ltl_spec
(* open MiddleParser.SyntaxCommon *)
open Program

(**
*)
module M 
      (AtomStore : Atom.S  
        with type 'a t = 'a (* imperative version for simplicity *)
        with type atom = ((Instant.instant option * ty, base_ty) fol_t, temp_f_prop) labeled
      ) 
      (* (F : Shared.Formula with type 'a t := FAtom.atom) *)
      (B:  BuchiSig.S 
      )
      (
        (* requires explicit passing because BProd is effectful *)
        BProd: BuchiSig.S
        with 
        type E.label = string bool_a BaProduct.arc_data and 
        type vdata = BaProduct.vertex_data
        ) 
        : GenSig.TriplesSig with
        type local_spec = base_spec_t and
        type temp_spec = ((temp_f_prop, Instant.instant option * Shared.ty, Shared.base_ty) temp_spec_t, temp_f_prop) labeled and
        type automaton = BProd.t  and
        type t = ((( ((Instant.instant option * Shared.ty, Shared.base_ty) fol_t, fol_data) U.labeled, formula_data) labeled cnf, cnf_data) hoare_triple, triple_data) labeled conjunction
        
  = struct
  module BUtils = BuchiSig.Utils (B)

  (* triples are generated from the product automaton *)
  type automaton = BProd.t

  type temp_spec = ((temp_f_prop, Instant.instant option * Shared.ty, Shared.base_ty) temp_spec_t, temp_f_prop) labeled

  type local_spec = base_spec_t

  (* triples contains formulas with the following type*)
  type formula = ((Instant.instant option * Shared.ty, Shared.base_ty) fol_t, fol_data) U.labeled


  type nonrec formula_data = formula_data

  (* final form of triples *)
  type t = (((formula, formula_data) labeled cnf, cnf_data) hoare_triple, triple_data) labeled conjunction



  let atom_of_label (m: AtomStore.atom -> formula) : string bool_a -> formula = 
    fun x -> 
      let f = map_formula (fun a ->  m AtomStore.(map snd (get_atom a))) x in
      (*fixme: do not remove labels *)
      mk_labeled ~label:{fol_data=Instant.min_nb_instant_dft} (fol_of_bool_a (fun x -> x.value) f) 
  


  (** [previous_instant_spec in_e init_post] produces the set of state formulas that must hold for a set of (incoming) edges [in_e],
      optionally appending an additional formula [init_post] if the node is initial
  *)
  let previous_instant_spec (in_e,_v: BProd.edge disjunction * BProd.vdata) (init_post : base_spec_t option) : (formula, formula_data) labeled cnf =
    let replace_i (v, (inst,(cty,bty))) =
        match inst,cty with
        (* no past *)
        | None,Input | None,Output -> 
            (* input/output is not the current instant input/output but the previous one*)
            (v, (Some (Previous 1), (cty,bty)))
        | None, State ->
            (* state variables are for the current instant as they are not modified in-between instants  *)
            (v, (inst,(cty,bty)))
        |None, Local -> (v, (inst,(cty,bty))) (* quantification over history *)
        | Some inst,_ ->
            let inst =
              match inst with
              | Previous n ->
                  (* we are at the next instant, so previous values are 1 instant earlier *)
                  Previous (n + 1)
              | At _ -> inst (* nothing to do if we mention a specific instant *)
            in
            (v, (Some inst, (cty,bty)))
    in
    (* get the possible states to be in from the previous transition second component *)
    map_disjuncts
      (fun e ->
        let l = BProd.E.label e in
        (* 'ensures' here will become requires, so the instant quantification is over history length + 1: 
            annotate the formula to get the correct history quantification when converting back to fol *)
        let nb_instant =
          add_nb_instant 1 BProd.(get_vdata (E.src e)).v_min_nb_instants
        in
        mk_labeled ~label:{eba_data=nb_instant} l.arc_f.ensures)
      in_e
      
    (* if an input led to no restriction on the state, then there is no need
              to put the other possible states.
              Indeed, if we prove the new state is independent of the current state,
              there is no need to check for others.
          *)
    (* if List.exists (fun (f,_) -> BoolA.(DnfBASet.exists (fun a -> a= AtomicBASet.singleton True) f.disjuncts)) l then [] else l *)

    |> fun (disj : (string bool_a, eba_data) labeled disjunction) ->

    (* the minimum number of instants of each eba is the maximum of all the minimum of the atoms  *)
    (* assert (List.fold_left (fun acc x -> Int.min acc x.label.eba_data.nb_instant) Int.max_int disj.disjuncts = v.v_min_nb_instants.nb_instant); *)

    map_disjuncts (fun d ->       
      let value = (atom_of_label @@ (map_value @@ map_fol_pred @@ map_expr Fun.id replace_i >> map_label @@ fun _ -> {fol_data=min_nb_instant_dft})) d.value
      and label = {formula_data=d.label.eba_data} (* now the label is over a formula *)
      in 
      mk_labeled ~label value    
    ) disj
      
    |> fun (disj : (formula, formula_data) labeled disjunction) ->

    (* if the current node is initial, add the setup postcondition to the disjunction *)
    Option.fold init_post
      ~none:disj 
      ~some:(fun (spec : base_spec_t) -> 
        let spec : formula = 
            let pred = map_fol_pred_ty Fun.id (map_expr Fun.id (fun (id,(cat,t)) -> id,(cat,t))) spec
            and label = {fol_data=min_nb_instant_dft}
            in mk_labeled ~label pred 
        in 

        let spec : (formula, formula_data) labeled =  
          let label = {formula_data = { nb_instant = 0; is_max = true }} in
          mk_labeled ~label spec
         
        in add_disjunct spec disj
      ) 
      
    |> fun (disj : (formula, formula_data) labeled disjunction) -> 
     mk_conj [disj]


    (* if a variable from the current node precondition or postcondition refers to the instant n and we know we are at this instant, 
      remove the temporal quantification
      fixme: if nb_instant is >= n, should we create two new nodes, one where 
        it is reached for the first time (instant = n) and one where it is reached again (instant > n) ? 
      *)

    let [@warning "-4"] at_current_instant_replace_post (v: BProd.vdata) : ('a,'b) fol_t -> ('a,'b) fol_t =
      if v.v_min_nb_instants.is_max then
        map_fol_pred 
          (map_expr Fun.id (fun (id, (inst,t)) ->
              match inst with
              | Some (At n) when n = v.v_min_nb_instants.nb_instant ->
                  (* if a variable refers to the current instant, remove the instant quantification *)
                  (id, (None,t))
              | _ -> (id, (inst,t))))
              
      else Fun.id


  (** [generate_node_spec inputs in_e out_e init_post] builds the list of hoare pairs
      for a node of the product graph
      - [inputs : (string * ty) list] inputs of the program
      - [in_e : PG.edge list] entry arcs
      - [out_e : PG.edge list] exit arcs
      - [init_post] the initial formula if the node is a start node

      For each input formula occuring in exit arcs, computes \{(g_1 \/ ... \/ g_n)
      /\ <init_post> /\ f\} \{ g_1' \/ ... \/ g_m'\} where (., g_i') are in in_e
      and (f,g_i) are in out_e and init is there if defined. *)
  let generate_node_spec
      ((in_e, v, out_e) : BProd.edge disjunction * BProd.vertex * BProd.edge disjunction)
      (init_post : base_spec_t option) :
      ((formula, formula_data) labeled cnf, cnf_data) hoare_triple conjunction =
    
    (* a state always has a successor *)
    assert (not (List.is_empty out_e.disjuncts));
    
    (* apart from the initial node, a state always has a predecessor *)
    assert ((not (List.is_empty in_e.disjuncts)) || BProd.is_start_node v);

    let vdata = BProd.get_vdata v in

    (* create a map binding the exit-arc rely formula to all its guarantee ones *)
    let module M = Map.Make (struct
      type t = (string bool_a, eba_data) labeled

      let compare (e1 : t) (e2 : t) =
        (* let open Format in  *)
        Stdlib.compare e1 e2
    end) in

    (* adapt previous ensures to the current instant *)
    let previous_ens : (formula, formula_data) labeled cnf = previous_instant_spec (in_e,vdata) init_post in

    let m : (string bool_a, eba_data) labeled disjunction M.t =
      (* Factorize exit arcs by common first component by buildin a map from
        first components to matching second components *)
      let add_v_info = mk_labeled ~label:{eba_data=vdata.v_min_nb_instants} in
      List.fold_left
        (fun m e ->
          let l = BProd.E.label e in
          let key = add_v_info l.arc_f.requires
          and data = add_v_info l.arc_f.ensures in 
          M.update key Option.(fold ~none:(disj_singleton data |> some) ~some:(add_disjunct data >> some)) m
          )
        M.empty out_e.disjuncts
    in

    (* construct the spec for each first component
    *)
    let mk_spec (req : (string bool_a, eba_data) labeled) (ens : (string bool_a, eba_data) labeled disjunction) 
           : ((formula, formula_data) labeled cnf, cnf_data) hoare_triple conjunction -> ((formula, formula_data) labeled cnf, cnf_data) hoare_triple conjunction =

        let requires : (formula, formula_data) labeled cnf  =
          (*  predicate on possible states of current node, 
              every input and output variables refer to the beginning and the end of the previous instant, respectively.    
          *)
          let previous_req : (formula, formula_data) labeled cnf = previous_ens
          and current_req : (formula, formula_data) labeled cnf = 
              let value = (atom_of_label @@ (map_value @@  at_current_instant_replace_post vdata >> map_label @@ fun _ -> {fol_data=min_nb_instant_dft})) req.value
              and label = {formula_data=req.label.eba_data} (* now the label is over a formula *)
              in {value;label} |> disj_singleton |> conj_singleton
          in
          let reqs = previous_req.conjuncts@current_req.conjuncts in 
          (* List.filter (function
            | { disjuncts = [f] } -> f.value.value <> FOL_True
            | { disjuncts = [] } -> false
            | _ -> true) reqs |> |> mk_conj *)
            mk_conj reqs 

        and ensures : (formula, formula_data) labeled cnf =
          (* disjunction of output properties sharing the same input property *)
          (*let disjuncts =
             if List.exists (fun (f, _) -> f = True) ens then
              (* if one of them is true, nothing to ensure *)
              []
            else fol_of_dnf_boola_replace ens
          in *)
          map_disjuncts (fun ens ->       
              let value = (atom_of_label @@ (map_value @@  at_current_instant_replace_post vdata >> map_label @@ fun _ -> {fol_data=min_nb_instant_dft})) ens.value
            and label = {formula_data=ens.label.eba_data} (* now the label is over a formula *)
            in {value;label}
          ) ens |> conj_singleton
        in
        (* if List.for_all (fun d -> List.is_empty d.disjuncts) ensures.conjuncts then
          (* discard when postcondition is true *) s
        else { requires; ensures } :: s *)
        add_conjunct @@ mk_labeled ~label:{cnf_data=vdata.v_min_nb_instants} { requires; ensures }
    in
    M.fold mk_spec m conj_empty

  let generate_triples (p : _ program) (a : BProd.t) : t =

    let aux (v: BProd.vertex) : t  =
      (* provide init post-condition for first node 
        we still return [true] in case there is no setup postcondition to ensure the first instant case
        is covered
      *)
      let extra_req : base_spec_t option =
        if BProd.is_start_node v then
          Option.(
            fold p.prog_setup 
            ~none:(Some true_fol) 
            ~some:(fun setup ->
                fold_mjoin some
                  (fun x y -> bind (map and_fol y) (fun f -> map f x))
                  None setup.setup_ensures
                  )
                 
          )
        else None
      in

      let in_e = BProd.pred_e a v |> mk_disj in
      let out_e = BProd.succ_e a v |> mk_disj in

      let specs : ((formula, formula_data) labeled cnf, cnf_data) hoare_triple conjunction =
        generate_node_spec (in_e, v, out_e) extra_req
      in

      (* if two or more transition share the same input, but with different outputs,
              we naively generate one spec per involved transition *)
      List.mapi
        (fun i s ->
          let open Format in
          let index = if i <> 0 then sprintf "_%i" i else "" in
          let id = BProd.(id_of_vertex v) ^ index in
          let label = { triple_id = id ; invariants = p.prog_main.main_loop_inv; nb_instants = s.label.cnf_data } in
          mk_labeled ~label s)
        specs.conjuncts |> mk_conj
    in
    BProd.fold_vertex (aux >> append_conjuncts) a conj_empty
end
