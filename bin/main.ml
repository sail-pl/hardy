(* open ArduinoSyntax.Syntax *)
open ArduinoParser.Lexer
open ArduinoParser.Fol_parser
open ArduinoTranslation.Translate
open Why3

let config : Whyconf.config = Whyconf.init_config None
let main : Whyconf.main = Whyconf.get_main config
let env : Env.env = Env.create_env (Whyconf.loadpath main)

let parse_file file =
  let text, lexbuf = MenhirLib.LexerUtil.read file in
  try
    let ast = program tokenize lexbuf in
    ast
  with
  | Error ->
      Printf.printf "File \"%s\", \n\" \n%s\n\" \nsyntax error \n" 
        file @@ 
        String.(sub text lexbuf.lex_curr_p.pos_cnum (length text - lexbuf.lex_curr_p.pos_cnum)); 
      exit (-1)
  | Lexical_error msg ->
      Printf.printf "Lexical error: %s\n" msg; 
      exit(-1)

let () =
  if Array.length Sys.argv <> 2 then 
    begin
    Printf.printf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 1
    end 
  else 
    let filename = Sys.argv.(1) in
    let program = parse_file filename in
    let p = translate_program program in
    Format.printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) p;
    let _mods =  Typing.type_mlw_file env [] "myfile.mlw" p in
    ()


