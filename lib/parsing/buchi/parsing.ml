module L = Lexer
module P = Parser

let parse_automaton file =
  let text, lexbuf = MenhirLib.LexerUtil.read file in
   try
  let ast = P.automaton L.tokenize lexbuf in ast
with
| P.Error ->
    Printf.printf "File \"%s\", \n\" \n%s\n\" \nsyntax error \n" 
      file @@ 
      String.(sub text lexbuf.lex_curr_p.pos_cnum (length text - lexbuf.lex_curr_p.pos_cnum)); 
    exit (-1)
