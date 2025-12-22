open HardyFrontEnd
open Syntax
open Syntax.Fol
open Syntax.Program
open Syntax.Shared
open Syntax.Instant
open HardyMisc.Utils
open MiddleParser.SyntaxCommon


module M (TAtom: TseitinAtomSig) (B:  BuchiSig.S 
        with type 'a FAtom.t = 'a 
        and type TAtom.t = TAtom.t
        and type E.label = TAtom.t eba 
        and type FAtom.ty = instant option * Shared.ty
        and type FAtom.qty = Shared.base_ty
        )(
          (* requires explicit passing because BProd is effectful *)
          BProd: BuchiSig.S
        with type E.label = TAtom.t eba BaProduct.arc_data
        and type vdata = BaProduct.vertex_data
        ) : Sig.TriplesSig with 
            type fol_ty =  Shared.ty and
            type fol_qty = B.FAtom.qty and
            type fol_data = Instant.min_nb_instants and
            type automaton = BProd.t
        
  = struct
  module BUtils = BuchiSig.Utils (B)

  type automaton = BProd.t
  type fol_ty = Shared.ty
  type fol_qty = B.FAtom.qty
  type fol_data = Instant.min_nb_instants
  type 'a info = { v : 'a ; i : min_nb_instants }

  
let fol_of_eba (m:(_,_) fol_t -> (_,_) fol_t) : B.TAtom.t eba -> (_,_) fol_t = 
    fol_of_eba (fun a -> 
      let atom = if B.TAtom.is_generated a then 
        let name = Format.asprintf "p%s" (B.TAtom.get_atom_id a) in 
        mk_dummy_loc (FOL_Atom (Predicate {name;args=[]})) 
      else 
        B.TAtom.get_atom_id a |> B.FAtom.get_atom |> snd 
      in
      let atom = if B.TAtom.is_neg a then mk_dummy_loc (FOL_StdUnary (LNot,atom)) else atom in
      m atom
    
    )
    
  (* create a map binding the exit-arc rely formula to all its guarantee ones *)
  module M = Map.Make (struct
    type t = B.BA.t info

    let compare (e1 : t) (e2 : t) =
      (* let open Format in  *)
      Stdlib.compare e1 e2
  end)

  let previous_instant_spec (in_e: BProd.edge list disjunction) (init_post : base_spec_t option) : (ty, base_ty, min_nb_instants) inst_spec_t Sig.formula =
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
    List.map
      (fun e ->
        let l = BProd.E.label e in
        (* 'ensures' here will become requires, so the instant quantification is over history length + 1: 
        annotate the formula to get the correct history quantification when converting back to fol *)
        let nb_instant =
          add_nb_instant 1 BProd.(get_vdata (E.src e)).v_min_nb_instants
        in
        {v=l.arc_f.ensures; i=nb_instant})
      in_e.disjuncts
      
    (* if an input led to no restriction on the state, then there is no need
              to put the other possible states.
              Indeed, if we prove the new state is independent of the current state,
              there is no need to check for others.
          *)
    (* if List.exists (fun (f,_) -> BoolA.(DnfBASet.exists (fun a -> a= AtomicBASet.singleton True) f.disjuncts)) l then [] else l *)
    |> fun (disj : B.E.label info list) -> 
     List.map ( fun f -> 
            let to_fol (f : B.E.label ) : (instant option * ty, base_ty) fol_t = 
              f |> fol_of_eba (map_fol_pred (map_expr Fun.id replace_i))  in 
            (mk_labeled f.i (to_fol f.v) )
          ) disj
     |> fun disj ->
    (* if the current node is an init_node, add the setup postcondition to the disjunction *)
    Option.fold init_post
      ~none:disj 
      ~some:(fun spec -> 
        (mk_labeled { nb_instant = 0; is_max = true } spec)::disj ) 
      
    |> fun disj -> 
    mk_conj [mk_disj disj]


  (** [generate_spec inputs in_e out_e init_post] builds the list of hoare pairs
      for a node of the product graph
      - [inputs : (string * ty) list] inputs of the program
      - [in_e : PG.edge list] entry arcs
      - [out_e : PG.edge list] exit arcs
      - [init_post] the initial formula if the node is a start node

      For each input formula occuring in exit arcs, computes \{(g_1 \/ ... \/ g_n)
      /\ <init_post> /\ f\} \{ g_1' \/ ... \/ g_m'\} where (., g_i') are in in_e
      and (f,g_i) are in out_e and init is there if defined. *)
  let generate_spec
      ((in_e, v, out_e) : BProd.edge list disjunction * BProd.vdata * BProd.edge list disjunction)
      (init_post : base_spec_t option) :
      ((_, base_ty, min_nb_instants) inst_spec_t Sig.formula, fol_data) hoare_triple list =
    assert (not (List.is_empty out_e.disjuncts));

    (* assert ((not (List.is_empty in_e)) || Option.is_some init_post); *)

    (* get previous ensures and adapt them to the current instant *)
    let previous_ens = previous_instant_spec in_e init_post in

    (* if a variable from the current node precondition or postcondition refers to the instant n and we know we are at this instant, 
      remove the temporal quantification
      fixme: if nb_instant is >= n, should we create two new nodes, one where 
        it is reached for the first time (instant = n) and one where it is reached again (instant > n) ? 
      *)

    let at_current_instant_replace_post : ('a,'b) fol_t -> ('a,'b) fol_t =
      if v.v_min_nb_instants.is_max then
        map_fol_pred 
          (map_expr Fun.id (fun (id, (inst,t)) ->
              match inst with
              | Some (At n) when n = v.v_min_nb_instants.nb_instant ->
                  (* if a variable refers to the current instant, remove the instant quantification *)
                  (id, (None,t))
              | _ -> (id, (inst,t))))
              
      else Fun.id
    in

    let fol_of_eba_replace inst_rep :  B.BA.t info list -> (_,base_ty, min_nb_instants) inst_spec_t list disjunction =
      fun f -> List.map ( fun f -> 
        (mk_labeled f.i (fol_of_eba inst_rep f.v))
      ) f |> mk_disj
      in


    let m : B.BA.t info list M.t =
      (* Factorize exit arcs by common first component by buildin a map from
        first components to matching second components *)
      List.fold_left
        (fun m e ->
          let l = BProd.E.label e in
          M.add_to_list
            {v=l.arc_f.requires; i=v.v_min_nb_instants}
            {v=l.arc_f.ensures; i=v.v_min_nb_instants}
            m)
        M.empty out_e.disjuncts
    in
    (* construct the spec for each first component *)
    M.fold
      (fun (req : B.BA.t info)
          (ens : (B.BA.t info) list)
          (s :
            ((_, base_ty, min_nb_instants) inst_spec_t Sig.formula, fol_data) hoare_triple
            list) ->
        let requires : (_,base_ty, min_nb_instants) inst_spec_t Sig.formula  =
          (*  predicate on possible states of current node, 
              every input and output variables refer to the beginning and the end of the previous instant, respectively.    
          *)
          let current_req : (_, base_ty, min_nb_instants) inst_spec_t Sig.formula = 
            [fol_of_eba_replace at_current_instant_replace_post [req]]|> mk_conj in
               
             List.filter (function
                | { disjuncts = [f] } -> f.value.value <> FOL_True
                | { disjuncts = [] } -> false
                | _ -> true) (previous_ens.conjuncts@current_req.conjuncts) |> mk_conj

        and ensures : (_,base_ty, min_nb_instants) inst_spec_t Sig.formula =
          (* disjunction of output properties sharing the same input property *)
          (*let disjuncts =
             if List.exists (fun (f, _) -> f = True) ens then
              (* if one of them is true, nothing to ensure *)
              []
            else fol_of_dnf_boola_replace ens
          in *)
          [fol_of_eba_replace at_current_instant_replace_post ens] |> mk_conj
        in
        (* if List.for_all (fun d -> List.is_empty d.disjuncts) ensures.conjuncts then
          (* discard when postcondition is true *) s
        else { requires; ensures } :: s *)
        { requires; ensures ; data = v.v_min_nb_instants} :: s)
      m []

  let generate_triples (p : middleend_program) (a : BProd.t) :
      ((_,base_ty, min_nb_instants) inst_spec_t Sig.formula, triple_data_t)
      hoare_triple
      list =



    let aux v =
      (* provide init post-condition for first node 
        we still return [true] in case there is no setup postcondition to ensure the first instant case
        is covered
      *)
      let extra_req : (instant option * ty,base_ty) fol_t option =
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

      let vdata = BProd.get_vdata v in

      let specs =
        generate_spec (in_e, vdata, out_e) extra_req
      in

      (* if two or more transition share the same input, but with different outputs,
              we naively generate one spec per involved transition *)
      List.mapi
        (fun i s ->
          let open Format in
          let index = if i <> 0 then sprintf "_%i" i else "" in
          let id = BProd.(id_of_vertex v) ^ index in
          let data = { triple_id = id ; invariants = p.prog_main.main_loop_inv ; min_nb_instants = Some s.data } in
          { s with data})
        specs
    in
    BProd.fold_vertex (aux >> List.append) a []

end
