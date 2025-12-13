module Parser = HardyFrontEnd.Parsing
module Cli = HardyFrontEnd.Cli.Init

let main (type triple_data fol_data out_pgrm)
    (module Middle : HardyMiddleEnd.Sig.S
      with type triple_data = triple_data
       and type fol_data = fol_data)
    (module Back : HardyBackEnd.Sig.S
      with type triple_data = Middle.triple_data
       and type fol_data = Middle.fol_data
       and type out_pgrm = out_pgrm)
    (module Interactive : Sig.S
      with type program = Middle.in_program * out_pgrm
       and type triple =
         (
           ( FrontParser.SharedSyntax.ty, FrontParser.SharedSyntax.base_ty,
             fol_data )
           FrontParser.Program.inst_spec_t list
           HardyMisc.Utils.disjunction list
           HardyMisc.Utils.conjunction, triple_data )
         FrontParser.ProgramSyntax.hoare_triple) =
  let module Cli = Cli () in
  let module I = TUI.F (Interactive) in
  let module Back = HardyBackEnd.Sig.F (Back) in
  let translate_spec = HardyMiddleEnd.Sig.translate_spec (module Middle) in
  let info = Cli.get_info in
  if not Sys.(file_exists info.outdir) then Sys.mkdir info.outdir 0o755;
  let output_file = Filename.(concat info.outdir @@ basename info.file) in

  Format.printf "Parsing program and spec...@.";
  Parser.parse_file info.file |> fun p -> 
  Format.printf "Typing program and spec...@.";
  HardyFrontEnd.Typing.type_pgrm p |> fun t_pgrm ->
  Format.printf "Translating spec...@.";
  translate_spec info t_pgrm |> fun triples ->
  Format.printf "Translating program...@.";
  Back.translate_program t_pgrm triples |> fun pgrm ->
  Format.printf "Writing program...@.";
  Back.write_program output_file pgrm;
  Format.printf "Attempting automatic proof...@.";
  I.prove (t_pgrm,pgrm) triples

let () =
  let open HardyMiddleEnd in
  let open MiddleParser.SyntaxCommon in
  let open Automata in
  let open Buchi in
  let open Hoa2ba in
  let module TAtom = TAtom() in
  let module FAtom = Atom.Imperative (struct 
    open HardyFrontEnd.Syntax
    type t = Instant.min_nb_instants 
    type fol_ty = Instant.instant option * Shared.ty
    type fol_qty = Shared.base_ty
    let pp_fol_qty = HardyFrontEnd.Printer.pp_base_ty
    let pp_var fmt (id,(inst,_):string * fol_ty) : unit = HardyFrontEnd.Printer.pp_hist fmt (id,inst)
  end ) in
  let module B = Make(TAtom)(FAtom) in
  let module G = Generation.M(TAtom)(SpinHoaOutput)(B) in
  main
    (module G)
    (module HardyBackEnd.Why3Gen.M)
    (module ExternalProver.M(B))
