open MiddleParser.NcSyntax

module Algos (BA : BuchiSig.S with type E.label = string bform) = struct
  let succ_with_arc a s =
    List.concat_map
      (fun v -> List.map (fun e -> (e, v)) (BA.find_all_edges a s v))
      (BA.succ a s)

  (** [find_in_path (v,p) s'] returns
      - Some true if s' is in the path and and b tells if it is an accepting
        path
      - Some false if s' is in the path but it is not an accepting path
      - None if s' is not in the path *)
  let find_in_path (current, path) s' =
    let res =
      List.fold_left
        (fun acc n ->
          match acc with
          | Some _, _ ->
              acc (* short-circuit: we already found n is in the current path *)
          | None, b ->
              (* update acceptant state with the new path node *)
              let acc_p = b || BA.acceptant n in

              (* if the current path node is n, the result depends on the path acceptance *)
              let found = if BA.V.equal current n then Some acc_p else None in
              (found, acc_p))
        (None, BA.acceptant s')
        (* if s' is acceptant, then any loop found is acceptant *)
        path
    in
    (* if None, s' is not within the path
       if Some b, s' is in the path and b tells if it is an accepting path
    *)
    fst res

  (* returns an empty list if no acceptant path found
     the optional function [f] tells what edges are allowed to be taken
      [ne_path] must ne a non-empty list
  *)
  let acceptant_path_from (a : BA.t) ?(f : BA.E.t -> bool = fun _ -> true)
      (ne_path : BA.vertex list) : BA.vertex list =
    let rec aux path : BA.vertex list =
      (* check if any successor of s forms an accepting path, collecting those which are not part of the path *)
      let found, try_next =
        List.fold_left
          (fun ((found, try_next) as acc) s' ->
            if Option.is_some found then acc
            else
              (* short-circuit: one of the successor forms an acceptant path *)
              match find_in_path (List.hd path, path) s' with
              | None ->
                  ( None,
                    s' :: try_next
                    (* not part of the actual path, add s' to the neighbours to try next *)
                  )
              | Some true ->
                  ( Some (s' :: path),
                    try_next (* acceptant path, no need to go further *) )
              | Some false ->
                  ( None,
                    try_next
                    (* in the path but doesn't form one acceptant, no need to try it next *)
                  ))
          (None, [])
          (succ_with_arc a (List.hd path)
          |> List.filter_map (fun (e, v) -> if f e then Some v else None))
      in

      (* if one of the successors forms an accepting path, we stop, otherwise,
         we do a DFS over the succesors not part of the path *)
      Option.fold ~some:Fun.id
        ~none:
          ((* no accepting path found yet, we continue *)
           List.fold_left
             (fun acc s' ->
               if acc <> [] then acc (* short-circuit: accepting path found *)
               else aux (s' :: path))
             [] try_next)
        found
    in
    aux ne_path

  let print_path base p =
    (* base reversed is the first parth of the path and p reversed is the second *)
    if p = [] then Format.printf "not an accepting path"
    else
      Format.printf "accepting path: [%a]"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt " -> ")
           (fun fmt v -> Format.fprintf fmt "%s" BA.(string_of_vertex v)))
        List.(rev_append base (rev p))
end
