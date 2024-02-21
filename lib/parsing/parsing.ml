module L = Lexer
module NCL = Neverclaimlex

module type PARSER = sig
  type token = Tokens.token

  exception Error
  
  val program : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> ArduinoSyntax.Syntax.program
end

type parser_type = Fol | Pltl | Ltl

let parse_file (file,ptype) =
  let module P = (val (match ptype with 
    | Fol -> (module Fol_parser) 
    | Pltl -> (module Pltl_parser) 
    | Ltl -> (module Ltl_parser)) : PARSER
  ) in 

  let text, lexbuf = MenhirLib.LexerUtil.read file in
  try
    let ast = P.program L.tokenize lexbuf in
    ast
  with
  | P.Error ->
      Printf.printf "File \"%s\", \n\" \n%s\n\" \nsyntax error \n" 
        file @@ 
        String.(sub text lexbuf.lex_curr_p.pos_cnum (length text - lexbuf.lex_curr_p.pos_cnum)); 
      exit (-1)
  | L.Lexical_error (_pos,msg) ->
      Printf.printf "Lexical error: %s\n" msg; 
      exit(-1)

let parse_automaton file =
  let module P = Neverclaim in

  let text, lexbuf = MenhirLib.LexerUtil.read file in
   try
  let ast = P.automaton NCL.tokenize lexbuf in ast
with
| P.Error ->
    Printf.printf "File \"%s\", \n\" \n%s\n\" \nsyntax error \n" 
      file @@ 
      String.(sub text lexbuf.lex_curr_p.pos_cnum (length text - lexbuf.lex_curr_p.pos_cnum)); 
    exit (-1)
