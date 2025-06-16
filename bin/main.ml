module Parser = HardyFrontEnd.Parsing
module Cli = HardyFrontEnd.Cli.Init

let main (type triple_data) (type fol_data)
    (module Middle : HardyMiddleEnd.Sig.S
      with type triple_data = triple_data
       and type fol_data = fol_data)
    (module Back : HardyBackEnd.Sig.S
      with type triple_data = Middle.triple_data
       and type fol_data = Middle.fol_data) =
  let module Cli = Cli () in
  let translate_spec = HardyMiddleEnd.Sig.translate_spec (module Middle) in
  let module Back = HardyBackEnd.Sig.F (Back) in
  let info = Cli.get_info in
  if not Sys.(file_exists info.outdir) then Sys.mkdir info.outdir 0o755;
  let output_file = Filename.(concat info.outdir @@ basename info.file) in

  Parser.parse_file info.file |> HardyFrontEnd.Typing.type_pgrm |> fun p ->
  translate_spec info p |> Back.translate_program p
  |> Back.write_program output_file; if info.eval then HardyFrontEnd.Interpreter.(eval_pgrm p (module ConsoleBridge)) 

let () =
  main
    (module HardyMiddleEnd.Buchi.Generation.M)
    (module HardyBackEnd.Why3Gen.M)
