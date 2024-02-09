open Lexer
open Fol_parser

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