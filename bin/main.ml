module CliM = HardyFrontEnd.Cli
open HardyMisc.Utils

let main 
    (
      type parsing_out middle_pgrm middle_temp_spec middle_spec_data
      p_temp_spec p_local_spec
      t_temp_spec t_local_spec
      triple_data  out_pgrm in_fun in_spec automaton
    )
    (
      module Cli : CliM.CliSig
    )
    (
      module Parsing : HardyFrontEnd.Parsing.S with type out_t = parsing_out
    )
    (
      module Typing : HardyFrontEnd.FrontSig.Typing
        with type in_t = Parsing.out_t and
        type out_t = (middle_temp_spec, middle_spec_data, middle_pgrm) HardyFrontEnd.Syntax.Shared.prog_with_spec
    )
    (
      module Middle : HardyMiddleEnd.MidSig.S with
      (* with type temp_spec = Typing.out_temp_spec *)
      (* and type local_spec = Typing.out_local_spec *)
      type automaton = automaton and
      type in_pgrm = middle_pgrm and
      type temp_spec = middle_temp_spec and
      type spec_data = middle_spec_data
    )
    (
      module Triples : HardyMiddleEnd.Automata.GenSig.TriplesSig
      with type automaton = Middle.automaton
      (* and type local_spec = Middle.local_spec *)
      (* and type temp_spec = Middle.temp_spec *)
      and type in_t = (middle_temp_spec, middle_spec_data, middle_pgrm) HardyFrontEnd.Syntax.Shared.prog_with_spec
      and type out_t = ((in_spec, in_fun) HardyFrontEnd.Syntax.Shared.hoare_triple, triple_data) labeled conjunction
    )
    (
      module I : Interactive.Sig.S with 
      type program = Typing.out_t * out_pgrm  and
      type triples = Triples.out_t
    )
    (
      module Back : HardyBackEnd.BackSig.S with
      type temp_spec = Middle.temp_spec and
      type in_t = Typing.out_t and
      type out_t = out_pgrm and 
      type in_fun = in_fun and
      type in_spec = in_spec and
      type triple_data = triple_data
    )

  =
  let module Front = HardyFrontEnd in
  let module I = Interactive.TUI.F (I) in  
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
  Format.printf "Attempting automatic proof...@.";
  I.prove (t_pgrm,pgrm) triples

let () =
  let module Cli = CliM.Init () in
  match Cli.get_config.ltl_atom with
  | Direct -> 
    let open LoopyLang.Ltl in 
    let module Triples = Triples(Cli) in
    let module Interactive = Interactive(Cli) in
    let module Back = Back(Cli) in
    main 
    (module Cli)
    (module Parsing)
    (module Typing)
    (module Middle)
    (module Triples)
    (module Interactive)
    (module Back) 
  | PastLTL -> 
    let open LoopyLang.Ppltl in
    let module Triples = Triples(Cli) in
    let module Interactive = Interactive(Cli) in
    let module Back = Back(Cli) in
    main 
    (module Cli)
    (module Parsing)
    (module Typing)
    (module Middle)
    (module Triples)
    (module Interactive)
    (module Back)
