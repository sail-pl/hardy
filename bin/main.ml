module CliM = HardyFrontEnd.Cli
open HardyMisc.Utils

let main 
    (
      type 
      p_temp_spec p_local_spec
      t_temp_spec t_local_spec
      triple_data  out_pgrm in_fun in_spec automaton
    )
    (
      module Cli : CliM.CliSig
    )
    (
      module Parsing : HardyFrontEnd.Parsing.S 
      with type local_spec = p_local_spec
      and type temp_spec = p_temp_spec
    )
    (
      module Typing : HardyFrontEnd.FrontSig.Typing 
      with type in_local_spec = Parsing.local_spec
      and type in_temp_spec = Parsing.temp_spec 
      and type out_temp_spec = t_temp_spec
      and type out_local_spec = t_local_spec
    )
    (
      module Middle : HardyMiddleEnd.MidSig.S
      with type temp_spec = Typing.out_temp_spec
      and type local_spec = Typing.out_local_spec
      and type automaton = automaton
    )
    (
      module Triples : HardyMiddleEnd.Automata.GenSig.TriplesSig
      with type automaton = Middle.automaton
      and type local_spec = Middle.local_spec
      and type temp_spec = Middle.temp_spec
      and type t = ((in_spec, in_fun) HardyFrontEnd.Syntax.Program.hoare_triple, triple_data) labeled conjunction
    )
    (
      module Interactive : Sig.S with 
      type program = Middle.in_program * out_pgrm  and
      type triples = Triples.t
    )
    (
      module Back : HardyBackEnd.BackSig.S with
      type local_spec = Middle.local_spec and
      type temp_spec = Middle.temp_spec and
      type out_pgrm = out_pgrm and 
      type in_fun = in_fun and
      type in_spec = in_spec and
      type triple_data = triple_data
    )

  =
  let module Front = HardyFrontEnd in
  let module I = TUI.F (Interactive) in
  let module Back = HardyBackEnd.BackSig.F (Back) in
  
  let translate_spec = HardyMiddleEnd.MidSig.translate_spec (module Middle) (module Triples) in

  let config = Cli.get_config in
  if not Sys.(file_exists config.outdir) then Sys.mkdir config.outdir 0o755;
  let output_file = Filename.(concat config.outdir @@ basename config.file) in

  Format.printf "Parsing program and spec... (%s flavor)@." (CliM.string_of_ltl_atom_t config.ltl_atom);
  Front.Parsing.parse_file (module Parsing) config.file |> fun p -> 
  Format.printf "Typing program and spec...@.";
  Typing.type_pgrm p |> fun t_pgrm ->
  Format.printf "Translating spec...@.";
  translate_spec config t_pgrm |> fun triples ->
  Format.printf "Translating program...@.";
  Back.translate_program t_pgrm triples |> fun pgrm ->
  Format.printf "Writing program...@.";
  Back.write_program output_file pgrm;
  if not Cli.get_config.no_check then 
    begin
    Format.printf "Attempting automatic proof...@.";
    I.prove (t_pgrm,pgrm) triples
    end

let () =
  let module Cli = CliM.Init () in
  match Cli.get_config.ltl_atom with
  | Direct -> 
    let open ClassicLtl.Make(Cli) in 
    main 
    (module Cli)
    (module Parsing)
    (module Typing)
    (module Middle)
    (module Triples)
    (module Interactive)
    (module Back)
  | PastLTL -> 
    let open PpLtl.Make(Cli) in
    main 
    (module Cli)
    (module Parsing)
    (module Typing)
    (module Middle)
    (module Triples)
    (module Interactive)
    (module Back)