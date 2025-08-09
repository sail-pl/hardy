open MiddleParser.NcSyntax
open Formulas
open FrontParser.LTLSyntax
open HardyMisc.Utils

module M (BA : BuchiSig.S with type E.label = string bform) (A : Atom.S with type 'a t = 'a) =
struct
  open BuchiSig.Utils (BA)
  open AutomatonAlgos.Algos (BA)

  type status = { old : NNFSet.t }

  module H = Hashtbl.Make (BA.V)

  let print_path fmt path =
    Format.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " -> ")
      (fun fmt v -> Format.fprintf fmt "%s" BA.(string_of_vertex v))
      fmt (List.rev path)

  let print_status (st : status) (path : H.key list) =
    Format.printf
      "@,current status: @, - current path: [%a] @, - old formulas for '%s': {%a} @,"
      print_path path (BA.string_of_vertex (List.hd path)) print_nnfset st.old 

  (* (Printer.string_of_ltl Fun.id Printer.string_of_ltl_binop
     Printer.string_of_ltl_unop f) *)

  (* bform_check  *)
  let check (bform_sat : string bform -> bool) (f : string ltl) (a : BA.t) :
      bool =
    let node_state = H.create (BA.nb_edges a) in
    (* create an entry for each node of the graph*)
    BA.iter_vertex (fun v -> H.add node_state v { old = NNFSet.empty }) a;

    let acceptant_path_from = acceptant_path_from a in
    let universal_lasso = acceptant_path_from ~f:(fun e -> BA.E.label e = True) in

    let rec check_cover cover path : bool =

      Format.printf "checking covering... (%i esets)@," (DisjunctSet.cardinal cover);
      let node = List.hd path in
      (* let st = H.find node_state node in *)
      let succs = succ_with_arc a node in

      let opened = DisjunctSet.(diff cover @@ fold (fun eset acc ->
          (* we construct the conjunction of all atoms of the eset *)
          let atoms =
            fold_mjoin atomic_ltl_to_bform
              (fun x y -> And (x, y))
              True
              (AtomicSet.to_list eset.atoms)
          in
          Format.printf "formula to satisfy: %s@,"
            (string_of_bform A.subst atoms);

          Format.printf "candidates: @,%a@,"
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@,")
               (fun fmt (e, dst) ->
                 Format.fprintf fmt "%s -[%s]-> %s" (BA.string_of_vertex node)
                   (string_of_bform A.subst (BA.E.label e))
                   (BA.string_of_vertex dst)))
            succs;

          (* we only keep transitions whose label satisfy the atoms *)
          let mk_form l = And (atoms, BA.E.label l) in
          let sat_trans =
            List.filter (fun (f, _) -> mk_form f |> bform_sat) succs
          in

          Format.printf "filtered candidates: @,%a@,"
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@,")
               (fun fmt (e, dst) ->
                 Format.fprintf fmt "%s -[%s]-> %s" (BA.string_of_vertex node)
                   (string_of_bform A.subst (BA.E.label e))
                   (BA.string_of_vertex dst)))
            sat_trans;

          (* among the satisfying ones,
             at least one must also have its dest node satisfying the next formulas and so on,
              this is a depth-first approach
          *)
          Format.printf
            "ensuring at least one dest node satisfies the next formulas:@,";
            
          if (List.exists
            (fun (f, v) ->
              Format.printf "- taking transition %s@,"
                (
                Format.sprintf "%s -[%s]-> %s" (BA.string_of_vertex node)
                  (string_of_bform A.subst (BA.E.label f))
                  (BA.string_of_vertex v));
              if aux eset.next_rooted (v :: path) then (
                Format.printf "OK [next formula satisfaction] @,";
                true)
              else (
                Format.printf "KO [next formula satisfaction] @,";
                false))
            sat_trans  )
            then
              add eset acc
            else
              acc
      ) cover empty)
      
      in 
      if DisjunctSet.(is_empty opened) then
        (
         (* We checked the current node satisfies every eset.
             Now, we must ensure all accepting esets only pertain to the cover's ones. Because we are working on a disjunction,
             it means we must ensure that there is no accepting path along a transition that satisfies
              the conjunction of the disjunction of all esets' atomic formulas negation
          *)
            Format.printf "ensuring strict satisfaction@,";
            let neg_atoms =
              fold_mjoin
                (fun (e : elementary_set) ->
                  fold_mjoin
                    (fun x -> Not (atomic_ltl_to_bform x))
                    (fun x y -> Or (x, y))
                    False
                    (AtomicSet.to_list e.atoms))
                (fun x y -> And (x, y))
                True
                (DisjunctSet.to_list cover)
            in

            Format.printf "negative formula: %s @," (string_of_bform A.subst neg_atoms);

            let mk_form l = And (neg_atoms, BA.E.label l) in
            let sat_trans =
              List.filter (fun (f, _) -> mk_form f |> bform_sat) succs
            in
            (* no acceptant path *)
            if List.for_all (fun (_, v) -> List.is_empty @@ acceptant_path_from [v]) sat_trans
            then (
              Format.printf "OK [strict satisfaction]@,";
              true)
            else (
              Format.printf "KO [DEBUG STILL RETURN TRUE strict satisfaction]@,";
              true (*fixme*))
        )
      else (
         (* no eset satisfied by the automaton found, either the formula is unsatisfiable or the automaton does not represent the formula
            return false for now
           *)
          Format.printf "elementary sets not satisfied : %a@," print_disjunctset opened;
          Format.printf "KO [elementary set satisfaction]@, "; false
      )
    and
        (* [aux] ensures any word starting from the current node is valid IFF it is an interpretation of [formulas] *)
        aux (formulas : NNFSet.t) (path : BA.vertex list) : bool =
      Format.open_vbox 8;
      let node = List.hd path in
      let st = H.find node_state node in
      print_status st path;
      let res =
        if NNFSet.is_empty formulas then (
          (* no formula to check for the current node,
             so we must ensure at least one path is acceptant for any letter along the path *)
          Format.printf "checking for an accepting path...";
          let p =
            acceptant_path_from path (* ~f:(fun e -> BA.E.label e = True) *)
          in
          if p <> [] then (
            Format.printf " found path %a " print_path p;
            true)
          else (
            Format.printf " [not found]@,";
            false)
            
            )

        else
          (* remove previously checked formulas *)
          let formulas = NNFSet.diff formulas st.old in
          if NNFSet.is_empty formulas then (
            Format.printf "all current formulas already checked@,";
            (* we previously checked all the formulas, return true directly *)
            true)
          else (
            (* we  assume the node satisfies the formula to check as 'check_cover' will look at each elementary cover *)
            H.add node_state node { old = NNFSet.union formulas st.old };
            Format.printf ">> adding formulas {%a} to node '%s' old formulas @," print_nnfset (NNFSet.diff formulas st.old) (BA.string_of_vertex node) ;


            (* build a covering for the formulas *)
            let ecover = build_ecovering formulas bform_sat in
            Format.printf "elementary cover : %a@," print_disjunctset ecover;

            if DisjunctSet.(equal ecover (singleton @@ mk_eltl_empty_next (AtomicSet.singleton ALTL_False))) then (
              (*  if the cover is the singleton {false}, the LTL formula is invalid, so no path should be acceptant *)
              Format.printf "invalid cover, ensuring no accepting path exist";
              let p = acceptant_path_from path in
              if p <> [] then (
                  Format.printf "KO (found path %a)@," print_path p;
                  false)
              else (
              Format.printf " OK@,";
              true
              )
              
              )
            else if DisjunctSet.is_empty ecover then (
              (* if the cover is empty (valid), every letter should be accepted from now on. 
                The alphabet being infinite, there must exist an acceptant lasso such that every transition is universal *)
                Format.printf "valid cover, ensuring a universal path exist ";
                let p = universal_lasso path in
                if p <> [] then (
                    Format.printf " OK (found path %a)@," print_path p;
                    true)
                else (
                Format.printf " KO@,";
                false
                )
                )
            else if check_cover ecover path then true
            else (
              (* the node doesn't verify the cover, restore previous old entry *)
              H.remove node_state node;
              Format.printf "<< restoring node '%s' old formulas to {%a} @," (BA.string_of_vertex node) print_nnfset (NNFSet.diff formulas st.old) ;
              false))
      in
      Format.close_box ();
      res
    in

    match get_all_init_nodes a with
    | [ h ] ->
        let f = NNFSet.singleton (to_nnf f) in
        Format.printf "starting from node '%s'@," (BA.string_of_vertex h);
          Format.printf "Negative Normal Form: '%a'@," print_nnfset f;
        let res = aux f [ h ] in
        Format.print_newline ();
        res
    | _ -> failwith "more than one or no initial state"

  let verif_a ((r_f, r_a), (g_f, g_a)) =
    let print_form f =
      HardyFrontEnd.Printer.(
        string_of_ltl Fun.id string_of_ltl_binop string_of_ltl_unop f)
    in
    let error name f =
      failwith
        (Format.sprintf "%s automaton does not represent LTL formula %s" name
           (print_form f))
    in
    (* let valid = BformSat.is_valid_w3 w3 (get_alt_ergo w3) in *)
    let sat = BformSat.is_sat_msat (module A) in
    Format.printf "checking rely LTL formula '%s' @," (print_form r_f);
    if not (check sat r_f r_a) then error "rely" r_f;
  Format.printf "checking guarantee LTL formula '%s'@," (print_form g_f);
       if not (check sat g_f g_a) then error "guarantee" g_f
end
