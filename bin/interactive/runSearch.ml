module F (I : Sig.S) = struct
  (* fixme: default hashing used here, which has limitations *)
(* 
  module TTable = Hashtbl.Make(struct 
    type t = I.triple 
    let equal = I.triple_eq 
    let hash = I.triple_hash
  end) *)

  type triples_status = (I.triple, I.proof_result) Hashtbl.t

  let run program funs =
    Format.print_flush ();
    let status = I.init_backend program in
    let vcs = I.get_vcs status funs in
    List.iter
      (fun vc ->
        match I.prove status vc with
        | Success -> Format.printf "OK@."
        | Failure msg ->
            (* Progress.interject_with (fun () -> TUUi.start_ui msg) *)
            Format.printf "KO: %s@. " msg)
      vcs
end
