open HardyFrontEnd
open Syntax
open Syntax.Fol
open Syntax.Program
open Syntax.Shared
open HardyMisc.Utils
open MiddleParser.NcSyntax
module Atom = Atom.Imperative ()
module B = Ba.Make (Atom)
module DotB = BuchiSig.Dot (B)
module BProd = BaProduct.Make (B) (Atom)
module DotBProd = BuchiSig.Dot (BProd)

let fol_vars : (expr, ty) fol -> string list =
  fold_fol (fun _ acc -> acc) expr_vars []

(* create a map binding the exit-arc rely formula to all its guarantee ones *)
module M = Map.Make (struct
  type t = string bform

  let compare e1 e2 =
    String.compare (e1 |> string_of_bform Fun.id) (e2 |> string_of_bform Fun.id)
end)

(** [generate_spec inputs in_e out_e init_post] builds the list of hoare pairs
    for a node of the product graph
    - [inputs : (string * ty) list] inputs of the program
    - [in_e : PG.edge list] entry edges
    - [out_e : PG.edge list] exit edges
    - [init_post] the initial formula if the node is a start node

    For each input formula occuring in exit edges, computes \{(g_1 \/ ... \/
    g_n) /\ <init_post> /\ f\} \{ g_1' \/ ... \/ g_m'\} where (., g_i') are in
    in_e and (f,g_i) are in out_e and init is there if defined. *)
let generate_spec (inputs : (string * base_ty) list) (in_e : BProd.E.t list)
    (out_e : BProd.E.t list) (init_post : (expr, ty) fol option) :
    ty inst_spec_t list hoare_pair list =
  assert (not (List.is_empty out_e));
  assert ((not (List.is_empty in_e)) || Option.is_some init_post);

  (* variable values at previous instant *)
  let prev v = private_var ("prev_" ^ v) in

  let inputs = List.map (pair_map (Right (fun t -> (Input, t)))) inputs in

  let fol_of_bform m = fol_of_bform (fun a -> m (Atom.get a |> snd)) in

  let m =
    (* Factorize exit edges by common first component by buildin a map from
       first components to matching second components *)
    List.fold_left
      (fun m e ->
        let l = BProd.E.label e in
        M.add_to_list l.requires l.ensures m)
      M.empty out_e
  in
  (* construct the spec for each first component *)
  M.fold
    (fun (req : string bform) (ens : string bform list) (s : _ list) ->
      let requires =
        (* get the possible states to be in from the previous transition second component *)
        let in_e =
          let l = List.map (fun e -> (BProd.E.label e).ensures) in_e in
          (* if an input led to no restriction on the state, then there is no need
             to put the other possible states.
             Indeed, if we prove the new state is independent of the current state,
             there is no need to check for others.
        *)
          if List.mem True l then [] else l
        in

        (*  predicate on possible states of current node, 
              every input variable i is renamed to _prev_i as it does not refer to the current input
              but the previous one.
              Prev inputs are only useful if they help define the current state or last ouput.              
          *)
        let previous_ens =
          let prev_inputs : (string * ty) list ref = ref [] in
          let inputs_only : bool ref = ref true in
          let replace_i e =
            match e.value with
            | Var v -> (
                (* check if the variable is an input *)
                match List.assoc_opt v inputs with
                | Some (_, ty) ->
                    let prev_v = prev v in
                    (* rename the variable and add it to the prev inputs list *)
                    if not (List.mem_assoc prev_v !prev_inputs) then
                      prev_inputs := (prev_v, (Local, ty)) :: !prev_inputs;
                    { e with value = Var prev_v }
                | None ->
                    inputs_only := false;
                    e)
            | _ -> e
          in
          (* if this is an init node, the default value must be false because of the disjunction *)
          let default =
            if Option.is_some init_post then false_fol else true_fol
          in
          let ens =
            fold_mjoin
              (fol_of_bform (map_fol_pred (map_expr replace_i)))
              or_fol default in_e
          in
          let exists_ens =
            if List.is_empty !prev_inputs then
              (* nothing to do if there is no previous input mentioned *)
              ens
            else if !inputs_only then
              (* formula variables only refer to previous input, discard it*)
              default
            else exists_fol !prev_inputs ens
          in
          (* if this is an init_node, add the setup postcondition to the current triple precondition *)
          Option.fold init_post ~none:exists_ens ~some:(fun setup ->
              if exists_ens.value = FOL_False then setup
              else or_fol setup exists_ens)
        in

        (* remove any trivial precondition *)
        List.filter
          (fun r -> r.value <> FOL_True)
          [ previous_ens; fol_of_bform Fun.id req ]
      and ensures =
        (* disjunction of output properties sharing the same input property *)
        if List.mem True ens then
          (* if one of them is true, nothing to ensure *)
          []
        else [ fold_mjoin (fol_of_bform Fun.id) or_fol true_fol ens ]
      in
      if List.is_empty ensures then (* discard when postcondition is true *) s
      else { requires; ensures } :: s)
    m []

let generate_triples (p : base_program) (a : BProd.t) :
    (string fun_id, ty inst_spec_t list) hoare_triple list =
  BProd.fold_vertex
    (fun v l ->
      (let in_e = BProd.pred_e a v in
       let out_e = BProd.succ_e a v in
       (* provide init post-condition for first node *)
       let extra_req =
         if not (BProd.is_start_node v) then None
         else
           Option.(
             bind p.prog_setup (fun setup ->
                 fold_mjoin some
                   (fun x y -> bind (map and_fol y) (fun f -> map f x))
                   None setup.setup_ensures))
       in

       let specs = generate_spec p.prog_decls.env_input in_e out_e extra_req in
       (* if two or more transition share the same input, but with different outputs,
             we naively generate one spec per involved transition *)
       List.mapi
         (fun i s ->
           let open Format in
           let index = if i <> 0 then sprintf "_%i" i else "" in
           let id = BProd.(id_of_vertex v) ^ index in
           ({ id }, s))
         specs)
      @ l)
    a []
