module P = ArduinoParser.Parsing
open ArduinoTranslation
open Utils


let () =
  let w3 = init_why3 () in

  let module Cli = Cli() in
  let info = Cli.get_info in
  
  if not Sys.(file_exists info.outdir) then begin
    Sys.mkdir info.outdir 0o755
  end;

  let program = 
      P.parse_file info.file 
      |> Translation.translate_program info
  in

  let output_file = Filename.concat info.outdir @@ (Filename.basename info.file) ^ ".mlw" in 
  print_program program output_file ;

  try
    let _mods =  Why3.Typing.type_mlw_file w3.env [] "???" program in
    (* continue *)
    ()
  with Why3.Loc.Located (loc,e) ->
    Why3.Loc.error ~loc e


