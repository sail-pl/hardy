(** {1 Input Program Parsing} *)


(** type of the program parser *)
module type S = sig 
  include HardyMisc.Utils.PIPELINE
  exception Error (* parsing error *)

  val program : (Lexing.lexbuf -> FrontParser.Tokens.token) -> Lexing.lexbuf -> out_t
end


let parse_file (type t) 
  (
    module P : S with type out_t = t
  ) 
  file : P.out_t =
  let open FrontParser.Lexer (* we assume all parsers share the same lexer *) in
  let _text, lexbuf = MenhirLib.LexerUtil.read file in
  try
    let ast = P.program tokenize lexbuf in
    ast
  with
  | P.Error ->
      Format.printf "File \"%s\", line %i, character %i: syntax error@," file
        lexbuf.lex_curr_p.pos_lnum
        (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol);
      exit (-1)
  | Lexical_error (_pos, msg) ->
      Format.printf "Lexical error: %s@," msg;
      exit (-1)


