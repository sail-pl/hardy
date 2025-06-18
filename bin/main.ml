module Parser = HardyFrontEnd.Parsing
module Cli = HardyFrontEnd.Cli.Init

let main (type triple_data) (type fol_data)
    (module Middle : HardyMiddleEnd.Sig.S
      with type triple_data = triple_data
       and type fol_data = fol_data)
    (module Back : HardyBackEnd.Sig.S
      with type triple_data = Middle.triple_data
       and type fol_data = Middle.fol_data) =
  let module Front = HardyFrontEnd in
  let module P2Ba = HardyMiddleEnd.Buchi.Pg2ba.M in
  let module P2BaDot = HardyMiddleEnd.Buchi.BuchiSig.Dot (P2Ba) in
  let module Cli = Cli () in
  let info = Cli.get_info in
  Parser.parse_file info.file |> Front.Typing.type_pgrm |> fun p ->
  if not Sys.(file_exists info.outdir) then Sys.mkdir info.outdir 0o755;
  Out_channel.with_open_text Filename.(concat info.outdir info.file ^ ".dot")
  (fun o -> P2Ba.create p.prog_nodes |> P2BaDot.output_graph o);
  (if info.eval then
     Front.Interpreter.(
       eval_pgrm p (module Front.Interpreter.ConsoleBridge)));
  if info.verify then (
    let translate_spec = HardyMiddleEnd.Sig.translate_spec (module Middle) in
    let module Back = HardyBackEnd.Sig.F (Back) in
    let output_file = Filename.(concat info.outdir @@ basename info.file) in
    translate_spec info p |> Back.translate_program p
    |> Back.write_program output_file)

let () =
  main
    (module HardyMiddleEnd.Buchi.Generation.M)
    (module HardyBackEnd.Why3Gen.M)
