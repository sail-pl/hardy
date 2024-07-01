open HardySyntax
open Types
open Fol
open Syntax
open PromelaSyntax
open TranslateUtils
open Ltl2buchi
open Locations

(* create a map binding the exit-arc rely formula to all its guarantee ones *)
module M = Map.Make (struct
  type t = AS.bform

  let compare e1 e2 =
    String.compare (e1 |> string_of_bform Fun.id) (e2 |> string_of_bform Fun.id)
end)

(**   [make_prod_spec input in_e out_e init_post] 
      builds the list of [Ptree.spec] for a node of the product graph 
      - [input : (string * ty) list] inputs of the program  
      - [in_e : PG.edge list] entry edges 
      - [out_e : PG.edge list] exit edges 
      - [init_post] the initial formula if the node is a start node
      For each input formula occuring in exit edges, computes 
        {(g_1 \/ ... \/ g_n) /\ <init_post> /\ f} 
        { g_1' \/ ... \/ g_m'}
        where (., g_i') are in in_e and (f,g_i) are in out_e
        and init is there if defined. 
      *)
let make_prod_spec (input : (string * ty) list) (in_e : PG.E.t list)
    (out_e : PG.E.t list) (init_post : expr fol option) :
    expr fol list hoare_pair list =
  assert (not (List.is_empty out_e));
  assert ((not (List.is_empty in_e)) || Option.is_some init_post);

  let m =
    (* Factorize exit edges by common first component by buildin a map from
       first components to matching second components *)
    List.fold_left
      (fun m e ->
        let l = PG.E.label e in
        M.add_to_list l.requires l.ensures m)
      M.empty out_e
  in
  (* construct the spec for each first component *)
  M.fold
    (fun (k : bform) (d : bform list) s ->
      let requires =
        (* get the possible states for this node to be in *)
        let in_e = List.map (fun e -> (PG.E.label e).ensures) in_e  in

        (* if an input led to no restriction on the state, then there is no need
             to put the other possible states.
             Indeed, if we prove the new state is independent of the current state,
             there is no need to check for others.
          *)
        let in_e_opt = if List.mem True in_e then [] else in_e in


        let precond = fold_mjoin bform_to_fol or_fol true_fol in_e_opt in

        (* if this is an init_node, add it to the precondition *)
        let precond_init = Option.fold init_post ~none:precond ~some:(fun x -> and_fol precond x ) in

        (* existentially quantify inputs (if any) *)
        let input_exists = if input = [] then Fun.id else exists_fol input in
        (* remove any trivial precondition *)
        List.filter (fun r -> r.value <> FOL_True) [ input_exists precond_init; bform_to_fol k ]
        
      and ensures =
        (* disjunction of output properties sharing the same input property *)
        if List.mem True d then
          (* if one of them is true, nothing to ensure *)
          []
        else [ fold_mjoin bform_to_fol or_fol true_fol d ]
      in
      if List.is_empty ensures then (* discard when postcondition is true *) s
      else { requires; ensures } :: s)
    m []
