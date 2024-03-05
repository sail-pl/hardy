module L = Lexer
module P = Ltl_parser

let parse_file (file) =
  let _text, lexbuf = MenhirLib.LexerUtil.read file in
    try
      let ast = P.program L.tokenize lexbuf in ast
    with
    | P.Error ->
      Printf.printf "File \"%s\", line %i, character %i: syntax error\n" 
        file
        lexbuf.lex_curr_p.pos_lnum
        lexbuf.lex_curr_p.pos_cnum
      ;
      exit (-1)
    | L.Lexical_error (_pos,msg) ->
        Printf.printf "Lexical error: %s\n" msg; 
        exit(-1)