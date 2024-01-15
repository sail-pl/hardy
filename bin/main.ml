(* open ArduinoSyntax.Syntax *)
open ArduinoParser.Lexer
open ArduinoParser.Parser

let parse_file file =
  let channel = open_in file in
  let lexbuf = Lexing.from_channel channel in
  try
    let ast = program tokenize lexbuf in
    close_in channel;
    ast
  with
  | Error ->
      Printf.printf "Syntax error at offset %d\n" (Lexing.lexeme_start lexbuf); exit (-1)
  | Lexical_error msg ->
      Printf.printf "Lexical error: %s\n" msg; exit(-1)

let () =
if Array.length Sys.argv <> 2 then begin
  Printf.printf "Usage: %s <filename>\n" Sys.argv.(0);
  exit 1
end else begin
  let filename = Sys.argv.(1) in
  let _program = parse_file filename in
  Printf.printf "Successfully parsed the program:\n"
  (* List.iter (fun stmt -> Printf.printf "%s\n" (Simple_imp_ast.string_of_stmt stmt)) program *)
end