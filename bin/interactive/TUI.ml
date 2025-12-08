module Ui = struct
  open Nottui
  module W = Nottui_widgets

  let vcount1 = Lwd.var 0
  let vcount2 = Lwd.var 0
  let quit = Lwd.var false

  let button1 count =
    W.button (Printf.sprintf "(S)kip  (%d) " count) (fun () ->
        Lwd.set vcount1 (count + 1))

  let button2 count =
    W.button (Printf.sprintf "(P)rune %d" count) (fun () ->
        Lwd.set vcount2 (count + 1))

  let button1m = Lwd.map ~f:button1 (Lwd.get vcount1)
  let button2m = Lwd.map ~f:button2 (Lwd.get vcount2)
  let title msg = W.string (Printf.sprintf "Status : %s" msg)

  let buttons =
    Lwd_utils.pack Ui.pack_x [ button1m; Lwd.pure (Ui.space 1 0); button2m ]

  let layout msg =
    Lwd_utils.pack Ui.pack_y
      [ Lwd.pure (title msg); Lwd.pure (Ui.space 0 1); buttons ]

  let shortcuts =
    Ui.keyboard_area (function
      | `ASCII 's', _ ->
          Lwd.update (( + ) 1) vcount1;
          `Handled
      | `ASCII 'p', _ ->
          Lwd.update (( + ) 1) vcount2;
          `Handled
      | `ASCII 'q', _ ->
          Lwd.set quit true;
          `Handled
      | _ -> `Unhandled)

  let start_ui msg = Nottui_unix.run ~quit (Lwd.map ~f:shortcuts (layout msg))
end

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
