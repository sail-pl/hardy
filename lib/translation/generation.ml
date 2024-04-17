open HardySyntax.Types
open HardySyntax.Fol
open HardySyntax.Syntax
open HardySyntax.PromelaSyntax
open TranslateUtils
open Ltl2buchi

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
        let exists_dij =
          (* disjonction of second components with input universally quantified *)
          List.fold_left
            (fun acc e -> or_fol (bform_to_fol (PG.E.label e).ensures) acc)
            false_fol in_e
          |> exists_fol input
        in
        let with_init =
          (* if initial node, add ensures from setup  *)
          Option.fold init_post ~none:exists_dij ~some:(fun i ->
              or_fol i exists_dij)
        in
        [ and_fol with_init (bform_to_fol k) ]
      and ensures =
        (* disjunction of exit-arc post-condition sharing the same pre-condition *)
        [
          List.fold_left (fun acc f -> or_fol acc (bform_to_fol f)) false_fol d;
        ]
      in
      { requires; ensures } :: s)
    m []
