(** {1 Input Program Parsing} *)

module L = FrontParser.Lexer
module P = FrontParser.PgrmParser

let parse_file file =
  let _text, lexbuf = MenhirLib.LexerUtil.read file in
  try
    let ast = P.program L.tokenize lexbuf in
    ast
  with
  | P.Error ->
      Format.printf "File \"%s\", line %i, character %i: syntax error@," file
        lexbuf.lex_curr_p.pos_lnum
        (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol);
      exit (-1)
  | L.Lexical_error (_pos, msg) ->
      Format.printf "Lexical error: %s@," msg;
      exit (-1)
