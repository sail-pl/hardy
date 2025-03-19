module Parser = HardyFrontEnd.Parsing
module Cli = HardyFrontEnd.Cli.Init

let main (type fun_id)
    (module Middle : HardyMiddleEnd.Sig.S
      with type fun_id = fun_id
       and type ty = HardyFrontEnd.Syntax.Shared.ty)
    (module Back : HardyBackEnd.Sig.S
      with type fun_id = Middle.fun_id
       and type in_ty = Middle.ty) =
  let module Cli = Cli () in
  let translate_spec = HardyMiddleEnd.Sig.translate_spec (module Middle) in
  let module Back = HardyBackEnd.Sig.F (Back) in
  let info = Cli.get_info in
  if not Sys.(file_exists info.outdir) then Sys.mkdir info.outdir 0o755;
  let output_file = Filename.(concat info.outdir @@ basename info.file) in

  Parser.parse_file info.file |> HardyFrontEnd.Typing.type_pgrm |> fun p ->
  translate_spec info p |> Back.translate_program p
  |> Back.write_program output_file

let () =
  main
    (module HardyMiddleEnd.Buchi.Generation.M)
    (module HardyBackEnd.Why3Gen.M)
