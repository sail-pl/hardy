open HardyFrontEnd
open Syntax
open Syntax.Fol
open Syntax.Program
open Syntax.Shared
open Syntax.Instant
open HardyMisc.Utils
open MiddleParser.SyntaxCommon

module M(TAtom: TseitinAtomSig)(B:  BuchiSig.S 
        with type 'a FAtom.t = 'a 
        and type _ FAtom.data = min_nb_instants
        and type TAtom.t = TAtom.t
        and type E.label = TAtom.t eba
        )
        = struct
  module DotB = BuchiSig.Dot (B)
  module BProd = BaProduct.Make(B)
  module BProdU = BuchiSig.Utils (BProd)
  module DotBProd = BuchiSig.Dot (BProd)


  type 'a info = { v : 'a ; i : min_nb_instants }


  let pp_ltl_full =
    Printer.(pp_ltl
      (fun fmt p -> Format.pp_print_string fmt (B.FAtom.add_and_get p |> snd))
      pp_ltl_binop pp_ltl_unop)

  let pp_ltl_short =
    Printer.(pp_ltl
      (fun fmt p -> Format.pp_print_string fmt (B.FAtom.add_and_get p |> fst))
      pp_ltl_binop pp_ltl_unop)

  let from_ltl : _ Ltl.ltl -> string Ltl.ltl =
    Ltl.map_ltl_pred (fun p -> B.FAtom.add_and_get p |> snd)


let fol_of_eba (m:ty fol_t -> ty fol_t) : B.TAtom.t eba -> ty fol_t = 
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

  let previous_instant_spec (env: (cat_ty * base_ty) env) (in_e: BProd.edge list disjunction) (init_post : ty fol_t option) : (ty, min_nb_instants) inst_spec_t Sig.formula =
    let replace_i (e : _ expr) =
      match e.value with
      | Var (v, inst) as var ->
          let value =
            match inst with
            | None -> begin 
              (* no past *)
              match Bindings.find v env.env_variables |> fst with
              | Input | Output  -> 
                (* input/output is not the current instant input/output but the previous one*)
                Var (v, Some (Previous 1))
              | State ->
                (* state variables are for the current instant as they are not modified in-between instants  *)
                var
              | Local -> failwith "no local variable in spec"
              end                
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
    let disjunctions :  B.E.label info list disjunction =
      let l =
        List.map
          (fun e ->
            let l = BProd.E.label e in
            (* 'ensures' here are over history length + 1: 
            annotate the formula to get the correct history quantification when converting back to fol *)
            let nb_instant =
              add_nb_instant 1 BProd.(get_vdata (E.src e)).v_min_nb_instants
            in
            {v=l.arc_f.ensures; i=nb_instant})
          in_e.disjuncts
      in
      (* if an input led to no restriction on the state, then there is no need
                to put the other possible states.
                Indeed, if we prove the new state is independent of the current state,
                there is no need to check for others.
            *)
      (* if List.exists (fun (f,_) -> BoolA.(DnfBASet.exists (fun a -> a= AtomicBASet.singleton True) f.disjuncts)) l then [] else l *)
      l |> mk_disj
    in
    let disjunctions = 
     List.map ( fun f -> 
            let to_fol (f : B.E.label ) : ty fol_t = 
              f |> fol_of_eba (map_fol_pred (map_expr replace_i))  in 
            (to_fol f.v,f.i)
          ) disjunctions.disjuncts |> mk_disj
     in

    (* if the current node is an init_node, add the setup postcondition to the disjunction *)
    let disjunctions = 
    Option.fold init_post 
      ~none:disjunctions 
      ~some:(fun cond -> ([cond, { nb_instant = 0; is_max = true }])@disjunctions.disjuncts |> mk_disj) 

    in mk_conj [disjunctions]


    (* todo: use env to type variables *)
    (* let requires :  (ty, min_nb_instants) inst_spec_t Sig.formula = *)

  (** [generate_spec inputs in_e out_e init_post] builds the list of hoare pairs
      for a node of the product graph
      - [inputs : (string * ty) list] inputs of the program
      - [in_e : PG.edge list] entry arcs
      - [out_e : PG.edge list] exit arcs
      - [init_post] the initial formula if the node is a start node

      For each input formula occuring in exit arcs, computes \{(g_1 \/ ... \/ g_n)
      /\ <init_post> /\ f\} \{ g_1' \/ ... \/ g_m'\} where (., g_i') are in in_e
      and (f,g_i) are in out_e and init is there if defined. *)
  let generate_spec (env : (cat_ty * base_ty) env)
      ((in_e, v, out_e) : BProd.edge list disjunction * BProd.vdata * BProd.edge list disjunction)
      (init_post : ty fol_t option) :
      (ty, min_nb_instants) inst_spec_t Sig.formula hoare_pair list =
    assert (not (List.is_empty out_e.disjuncts));

    (* assert ((not (List.is_empty in_e)) || Option.is_some init_post); *)

    (* get previous ensures and adapt them to the current instant *)
    let previous_ens = previous_instant_spec env in_e init_post in

    (* if a variable from the current node precondition or postcondition refers to the instant n and we know we are at this instant, 
      remove the temporal quantification
      fixme: if nb_instant is >= n, should we create two new nodes, one where 
        it is reached for the first time (instant = n) and one where it is reached again (instant > n) ? 
      *)
    let at_current_instant_replace : ty fol_t -> ty fol_t =
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

    let fol_of_eba_replace :  B.BA.t info list -> (ty, min_nb_instants) inst_spec_t list disjunction =
      fun f -> List.map ( fun f -> 
        (fol_of_eba at_current_instant_replace f.v, f.i)
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
            (* 'ensures' exit arcs are over the start of the next instant  *)
            {v=l.arc_f.ensures; i=Instant.add_nb_instant 1 v.v_min_nb_instants}
            m)
        M.empty out_e.disjuncts
    in
    (* construct the spec for each first component *)
    M.fold
      (fun (req : B.BA.t info)
          (ens : (B.BA.t info) list)
          (s :
            (ty, min_nb_instants) inst_spec_t Sig.formula hoare_pair
            list) ->
        let requires : (ty, min_nb_instants) inst_spec_t Sig.formula  =
          (*  predicate on possible states of current node, 
              every input and output variables refer to the begining and the end of the previous instant, respectively.    
          *)
          let current_req : (ty, min_nb_instants) inst_spec_t Sig.formula = 
            [fol_of_eba_replace [req]]|> mk_conj in

          (* remove any trivial precondition *)
            (* (List.filter
              (function
                | { conjuncts = [ (f, _) ] } -> f.value <> FOL_True
                | { conjuncts = [] } -> false
                | _ -> true)
              [ previous_ens; current_req ]) *)
               
              (previous_ens.conjuncts@current_req.conjuncts) |> mk_conj

        and ensures : (ty, min_nb_instants) inst_spec_t Sig.formula =
          (* disjunction of output properties sharing the same input property *)
          (*let disjuncts =
             if List.exists (fun (f, _) -> f = True) ens then
              (* if one of them is true, nothing to ensure *)
              []
            else fol_of_dnf_boola_replace ens
          in *)
          [fol_of_eba_replace ens ] |> mk_conj
        in
        (* if List.for_all (fun d -> List.is_empty d.disjuncts) ensures.conjuncts then
          (* discard when postcondition is true *) s
        else { requires; ensures } :: s *)
        { requires; ensures } :: s)
      m []

  let generate_triples (p : base_program) (a : BProd.t) :
      ( triple_data_t,
        (ty, min_nb_instants) inst_spec_t Sig.formula )
      hoare_triple
      list =



    let aux v =
      (* provide init post-condition for first node *)
      let extra_req : ty fol_t option =
        if BProd.is_start_node v then
          Option.(
            let setup = find_start_node p.prog_nodes
            in
              fold_mjoin some
                (fun x y -> bind (map and_fol y) (fun f -> map f x))
                None setup.node_spec.ensures
          )
        else None
      in

      let in_e = BProd.pred_e a v |> mk_disj in
      let out_e = BProd.succ_e a v |> mk_disj in

      let vdata = BProd.get_vdata v in

      let specs =
        generate_spec p.prog_decls (in_e, vdata, out_e) extra_req
      in

      (* if two or more transition share the same input, but with different outputs,
              we naively generate one spec per involved transition *)
      List.mapi
        (fun i s ->
          let open Format in
          let index = if i <> 0 then sprintf "_%i" i else "" in
          let id = BProd.(id_of_vertex v) ^ index in
          let data = { triple_id = id; triple_node_id = Program.init_node } in
          (data, s))
        specs
    in
    BProd.fold_vertex (aux >> List.append) a []

end
