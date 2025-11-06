module L = HoaLexer
module P = HoaParser

let parse_automaton file =
  let text, lexbuf = MenhirLib.LexerUtil.read file in
  try
    let ast = P.automaton L.tokenize lexbuf in
    ast
  with P.Error ->
    (Format.printf "@[<v 0>File \"%s\", @,\" @,%s@,\"@,syntax error@,@]" file
    @@ String.(
         sub text lexbuf.lex_curr_p.pos_cnum
           (length text - lexbuf.lex_curr_p.pos_cnum)));
    exit (-1)
