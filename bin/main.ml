module P = ArduinoParser.Parsing
open ArduinoTranslation
open Utils

let () =
  let w3 = init_why3 () in

  let file = get_input_file () in 
  let filename = Filename.(file |> remove_extension |> basename) in 
  let dir = filename ^ "_gen" in
  
  (* drop generated files in $cwd/<filename>_gen/ *)
  let output_path = Filename.(concat (Sys.getcwd ()) dir) in

  let () = try Sys.mkdir output_path 0o755
          with Sys_error _ -> ()  (* if directory exists, continue *)
  in
  let output_file = Filename.concat output_path @@ filename ^ ".mlw" in 

  let program = 
      (file,P.Ltl)
      |> P.parse_file 
      |> Translate.LTL.translate_program output_path
  in
  print_program program output_file ;

  try
    let _mods =  Why3.Typing.type_mlw_file w3.env [] "???" program in
    (* continue *)
    ()
  with Why3.Loc.Located (loc,e) ->
    Why3.Loc.error ~loc e


