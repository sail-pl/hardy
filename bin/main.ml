(* open ArduinoSyntax.Syntax *)
module P = ArduinoParser.Parsing
module T = ArduinoTranslation.Translate
open Utils

let output_path = Filename.concat (Sys.getcwd ())

let () =
  let w3 = init_why3 () in

  let file = get_input_file () in 
  let filename = Filename.(file |> remove_extension |> basename) in 

  (* drops generated files in current directory for now*)
  let output_file = output_path @@ filename ^ ".mlw" in 
  let program = file
      |> P.parse_file 
      |> T.translate_program
  in
  print_program program output_file ;

  try
    let _mods =  Why3.Typing.type_mlw_file w3.env [] "???" program in
    (* continue *)
    ()
  with Why3.Loc.Located (loc,e) ->
    Why3.Loc.error ~loc e


