open HardyFrontEnd
open FrontSig
open Syntax
open Syntax.Fol
open Syntax.Shared
open Syntax.Instant
open HardyMisc.Utils
open Program


module M 
      (T : sig 
          include Types.T with 
        type transition_data = min_nb_instants and 
        type formula_data = min_nb_instants and
        type cnf_data = min_nb_instants and
        type base_spec_t = ((instant option * ty) expr, base_ty option) pred_fol and
        type triple_data = (triple_id : string * invariants : ((instant option * ty) expr, base_ty option) pred_fol list * nb_instants : Instant.min_nb_instants) and
        type ('ty,'qty) fol_t = ('ty expr, 'qty option) pred_fol
      end
      )
      (AtomStore : Atom.S  
        with type 'a t = 'a (* imperative version for simplicity *)
        with type atom = ((Instant.instant option * ty, base_ty) T.fol_t, temp_f_prop) labeled
      ) 
      (B:  BuchiSig.S 
      )
      (
        (* requires explicit passing because BProd is effectful *)
        BProd: BuchiSig.S
        with 
        type E.label = string bool_a BaProduct.arc_data and 
        type vdata = BaProduct.vertex_data
        ) 
        (Cli :  Cli.CliSig)
        : GenSig.TriplesSig with
        type local_spec = T.base_spec_t and
        type temp_spec = ((temp_f_prop, Instant.instant option * ty, base_ty) T.temp_spec_t, temp_f_prop) labeled and
        type automaton = BProd.t  and
        type t = (( ((Instant.instant option * ty, base_ty) T.fol_t, T.formula_data Types.formula_data) labeled cnf, T.cnf_data Types.cnf_data) hoare_triple, T.triple_data Types.triple_data) labeled conjunction
        
  = struct
  module BUtils = BuchiSig.Utils (B)

  (* triples are generated from the product automaton *)
  type automaton = BProd.t

  type temp_spec = ((temp_f_prop, Instant.instant option * ty, base_ty) T.temp_spec_t, temp_f_prop) labeled

  type local_spec = T.base_spec_t

  (* triples contains formulas with the following type*)
  type formula = ((Instant.instant option * ty, base_ty) T.fol_t, T.formula_data Types.formula_data) labeled


  (* final form of triples *)
  type t = ((formula cnf, T.cnf_data Types.cnf_data) hoare_triple, T.triple_data Types.triple_data) labeled conjunction


  (** [previous_instant_spec in_e init_post] produces the set of state formulas that must hold for a set of (incoming) edges [in_e],
      optionally appending an additional formula [init_post] if the node is initial
  *)
  let previous_instant_spec (in_e,_v: BProd.edge disjunction * BProd.vdata) (init_post : T.base_spec_t option) : formula cnf =
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
        mk_labeled ~label:Types.{transition_data=nb_instant} l.arc_f.ensures)
      in_e
      
    (* if an input led to no restriction on the state, then there is no need
              to put the other possible states.
              Indeed, if we prove the new state is independent of the current state,
              there is no need to check for others.
          *)
    (* if List.exists (fun (f,_) -> BoolA.(DnfBASet.exists (fun a -> a= AtomicBASet.singleton True) f.disjuncts)) l then [] else l *)

    |> fun (disj : (string bool_a, T.transition_data Types.transition_data) labeled disjunction) ->

    (* the minimum number of instants of each transition is the maximum of all the minimum of the atoms  *)
    (* assert (List.fold_left (fun acc x -> Int.min acc x.label.transition_data.nb_instant) Int.max_int disj.disjuncts = v.v_min_nb_instants.nb_instant); *)

    map_disjuncts (fun d ->  
        map_formula (fun a ->
          let atom = AtomStore.(map snd (get_atom a)) (* recover atoms *) in
          (map_fol_pred @@ map_expr Fun.id replace_i) atom.value  (* adjust temporal quantification *)
        ) d.value 
        |> fol_of_bool_a Fun.id (* flatten boolean algebra into fol *)
        |> mk_labeled ~label:Types.{formula_data=d.label.transition_data} (* enrich the formula with transition data *)
    ) disj
      
    |> fun (disj : formula disjunction) ->

    (* if the current node is initial, add the setup postcondition to the disjunction *)
    Option.fold init_post
      ~none:disj 
      ~some:(fun (spec : T.base_spec_t) -> 
        let spec : formula = 
            let pred = spec (* map_fol_pred_ty Fun.id (map_expr Fun.id Fun.id) spec *)
            and label = Types.{formula_data={ nb_instant = 0; is_max = true }} (* we are at the first instant if we executed the setup just before *)
            in mk_labeled ~label pred          
        in add_disjunct spec disj
      ) 
      
    |> fun (disj : formula disjunction) -> 
    mk_conj [disj]

    (* if a variable from the current node precondition or postcondition refers to the instant n and we know we are at this instant, 
      remove the temporal quantification
      fixme: if nb_instant is >= n, should we create two new nodes, one where 
        it is reached for the first time (instant = n) and one where it is reached again (instant > n) ? 
      *)

  let [@warning "-4"] at_current_instant_replace_post (v: BProd.vdata) : ('a,'b) T.fol_t -> ('a,'b) T.fol_t =
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
      (init_post : T.base_spec_t option) :
      (formula cnf, T.cnf_data Types.cnf_data) hoare_triple conjunction =
    
    (* a state always has a successor *)
    assert (not (List.is_empty out_e.disjuncts));
    
    (* apart from the initial node, a state always has a predecessor *)
    assert ((not (List.is_empty in_e.disjuncts)) || BProd.is_start_node v);

    let vdata = BProd.get_vdata v in

    (* create a map binding the exit-arc rely formula to all its guarantee ones *)
    let module M = Map.Make (struct
      type t = (string bool_a, T.transition_data Types.transition_data) labeled

      let compare (e1 : t) (e2 : t) =
        (* let open Format in  *)
        Stdlib.compare e1 e2
    end) in

    (* adapt previous ensures to the current instant *)
    let previous_ens : formula cnf = previous_instant_spec (in_e,vdata) init_post 
    in  

    let m : (string bool_a, T.transition_data Types.transition_data) labeled disjunction M.t =
      (* Factorize exit arcs by common first component by buildin a map from
        first components to matching second components *)
      let add_v_info = mk_labeled ~label:Types.{transition_data=vdata.v_min_nb_instants} in
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
    let mk_spec (req : (string bool_a, T.transition_data Types.transition_data) labeled) (ens : (string bool_a, T.transition_data Types.transition_data) labeled disjunction) 
           : (formula cnf, T.cnf_data Types.cnf_data) hoare_triple conjunction -> (formula cnf, T.cnf_data Types.cnf_data) hoare_triple conjunction =

        let requires : formula cnf  =
          (*  predicate on possible states of current node, 
              every input and output variables refer to the beginning and the end of the previous instant, respectively.    
          *)
          let previous_req : formula cnf = previous_ens
          and current_req : formula cnf = 
              map_formula (fun a ->
                let atom = AtomStore.(map snd (get_atom a)) (* recover atoms *) in
                (  at_current_instant_replace_post vdata) atom.value  (* adjust temporal quantification *)
              ) req.value 
              |> fol_of_bool_a Fun.id (* flatten boolean algebra into fol *)
              |> mk_labeled ~label:Types.{formula_data=req.label.transition_data} (* enrich the formula with transition data *)
              |> disj_singleton |> conj_singleton
          in
          let reqs = previous_req.conjuncts@current_req.conjuncts in 
          (* List.filter (function
            | { disjuncts = [f] } -> f.value.value <> FOL_True
            | { disjuncts = [] } -> false
            | _ -> true) reqs |> |> mk_conj *)
            mk_conj reqs 

        and ensures : formula cnf =
          (* disjunction of output properties sharing the same input property *)
          (*let disjuncts =
             if List.exists (fun (f, _) -> f = True) ens then
              (* if one of them is true, nothing to ensure *)
              []
            else fol_of_dnf_boola_replace ens
          in *)
          if Cli.get_info.smoke_tests then
              (* attempt to prove false *)
              mk_labeled ~label:Types.{formula_data=min_nb_instant_dft} false_fol |> disj_singleton |> conj_singleton 
          else
            map_disjuncts (fun ens ->      
              map_formula (fun a ->
              let atom = AtomStore.(map snd (get_atom a)) (* recover atoms *) in
                (at_current_instant_replace_post vdata) atom.value  (* adjust temporal quantification *)
              ) ens.value 
              |> fol_of_bool_a Fun.id (* flatten boolean algebra into fol *)
              |> mk_labeled ~label:Types.{formula_data=ens.label.transition_data} (* enrich the formula with transition data *)
            ) ens |> conj_singleton
        in
        (* if List.for_all (fun d -> List.is_empty d.disjuncts) ensures.conjuncts then
          (* discard when postcondition is true *) s
        else { requires; ensures } :: s *)
        add_conjunct @@ mk_labeled ~label:Types.{cnf_data=vdata.v_min_nb_instants} { requires; ensures }
    in
    M.fold mk_spec m conj_empty

  let generate_triples (p : _ program) (a : BProd.t) : t =

    let aux (v: BProd.vertex) : t  =
      (* provide init post-condition for first node 
        we still return [true] in case there is no setup postcondition to ensure the first instant case
        is covered
      *)
      let extra_req : T.base_spec_t option =
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

      let specs : (formula cnf, T.cnf_data Types.cnf_data) hoare_triple conjunction =
        generate_node_spec (in_e, v, out_e) extra_req
      in

      (* if two or more transition share the same input, but with different outputs,
              we naively generate one spec per involved transition *)
      List.mapi
        (fun i s ->
          let open Format in
          let index = if i <> 0 then sprintf "_%i" i else "" in
          let id = BProd.(id_of_vertex v) ^ index in
          let label = Types.{triple_data = (~triple_id:id,~invariants:p.prog_main.main_loop_inv, ~nb_instants:s.label.cnf_data)} in
          mk_labeled ~label s)
        specs.conjuncts |> mk_conj
    in
    BProd.fold_vertex (aux >> append_conjuncts) a conj_empty
end
