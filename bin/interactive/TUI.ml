module F (I : Sig.S) = struct
  let bar ~total =
    let open Progress.Line in
    list [const "proving" ; spinner (); bar ~style:`UTF8 total; count_to total ]

  let prove program funs =
    Format.print_flush ();
    let status = I.init_backend program in
    let vcs = I.get_vcs status funs in
    Progress.with_reporter
      (bar ~total:(List.length vcs))
      (fun pgrs ->
    List.iter
      (fun vc ->
        match I.prove status vc with
        | Success -> pgrs 1
        | Failure msg ->
            Progress.interject_with (fun () -> Format.printf "Failure: %s@. " msg)
        )
      vcs
      )
end
