open FrontParser.ProgramSyntax

(** {1 Input Program Parsing} *)


(** type of the program parser *)
module type S = sig 
  type temp_spec (* type of the temporal specification *)

  type local_spec (* type of the local specification *)

  type t = (temp_spec, unit, local_spec, unit, parsed_env) program (* type of the program *)

  exception Error (* parsing error *)

  val program : (Lexing.lexbuf -> FrontParser.Tokens.token) -> Lexing.lexbuf -> t
end


let parse_file (type temp_spec local_spec) 
  (
    module P : S with 
    type temp_spec = temp_spec and 
    type local_spec = local_spec
  ) 
  file : P.t =
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


