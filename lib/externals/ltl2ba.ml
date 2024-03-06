open ArduinoSyntax.PromelaSyntax
open BaParser.Parsing

(* Move to external tools *)
(* put info as global variable *)

type info = {
  file : string;
  ltl2baPath : string;
  verbose : bool;
  pltl_mode : bool;
  outdir : string;
}

let generate_claim (i : info) (never_file : string) (f : string) : unit =
  let cmd =
    Filename.quote_command i.ltl2baPath [ "-f"; f ] ~stdout:never_file
      ~stderr:(never_file ^ ".err")
  in
  if i.verbose then Format.printf "ltl2ba command line : %s" cmd;
  let ret =
    Sys.command
    @@ Filename.quote_command i.ltl2baPath [ "-f"; f ] ~stdout:never_file
      ~stderr:(never_file ^ ".err")
  in
  if ret <> 0 then
    failwith Format.(sprintf "non-0 exit-code (%i) from ltl2ba" ret)

let read_claim (never_file : string) : neverclaim =
    parse_automaton never_file
