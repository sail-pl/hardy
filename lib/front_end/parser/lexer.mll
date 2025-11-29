{
  open Tokens
  open Lexing

  exception Lexical_error of (position * position) * string
  exception Syntax_error of (position * position) * string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                pos_lnum = pos.pos_lnum + 1
      }

  let pos_range lexbuf = 
    let sp = lexeme_start_p lexbuf and ep = lexeme_end_p lexbuf in 
    sp,ep

}


let digit = ['0'-'9']
let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']
let letter = (lowercase | uppercase)
let lid = lowercase (letter|digit|'_')*
let uid = uppercase (letter|digit|'_')+ (* minimum two letters to distinguish from temporal op *)
let newline = '\r' | '\n' | "\r\n"


rule tokenize = parse
  | [' ' '\t']              { tokenize lexbuf }  (* Skip whitespaces *)
  | "//"                    { read_single_line_comment lexbuf }
  | "/*"                    { read_multi_line_comment lexbuf }
  | "unit"                  { TY_UNIT }
  | "bool"                  { TY_BOOL }
  | "int"                   { TY_INT } 
  | "string"                { TY_STRING }
  | "array"                 { TY_ARRAY }
  | "true"                  { LTRUE  } 
  | "false"                 { LFALSE }
  | "if"                    { IF }
  | "then"                  { THEN }
  | "else"                  { ELSE }
  | "while"                 { WHILE }
  | "do"                    { DO  }
  | "end"                   { END }
  | "done"                  { DONE }
  | "node"                  { NODE }
  | "return"                { RETURN }
  (*| "var"                   { VAR }
  | "input"                 { INPUT }
  | "output"                { OUTPUT }*)
  | "assumes"               { ASSUMES }
  | "guarantees"            { GUARANTEES }
  | "requires"              { REQUIRES }
  | "prev"                  { PREV }
  (* | "^"                     { HAT } *)
  (* | "any"                   { ANY } *)
  (* | "?"                     { QMARK } *)
  (* | "all"                   { ALL } *)
  | "#"                     { SHARP }
  | "$"                     { DOLLAR }
  | "at"                    { AT }
  | "@"                     { SYMB_AT }
  | "last"                  { LAST }
  | "first"                 { FIRST }
  | "start"                 { START }
  | "ensures"               { ENSURES }
  | "invariant"             { INVARIANT }
  | "variant"               { VARIANT }
  | "forall"                { FORALL }
  (* | "exists_prev"           { EXISTS_PREV } *)
  | "exists"                { EXISTS }
  | "("                     { LPAREN }
  | ")"                     { RPAREN }
  | "{"                     { LBRACE }
  | "}"                     { RBRACE }
  | "["                     { LSQBRACE }
  | "]"                     { RSQBRACE }
  (* | "nothing"               { NOTHING } *)
  | "|"                     { SEP }
  | ";"                     { SEMI }
  | ":="                    { ASSIGN }
  (* | "."                     { DOT } *)
  | "!"                     { EMARK }
  | "+"                     { PLUS }
  | "-"                     { MINUS }
  | "*"                     { TIMES }
  | "/"                     { DIVIDE }
  | "="                     { EQ }
  | "<>"                    { NEQ }
  | ">"                     { GT }
  | "<"                     { LT }
  | ">="                    { GTE }
  | "<="                    { LTE }
  | "tt"                    { TRUE }
  | "ff"                    { FALSE }
  | ";"                     { SEMI }
  | ":"                     { COLON }
  | ","                     { COMMA }
  (* | "S"                     { SINCE } *)
  | "X"                     { NEXT }
  | "U"                     { UNTIL}
  | "R" | "V"               { RELEASE }
  | "M"                     { SRELEASE }
  | "F"                     { EVENTUALLY }
  | "G"                     { ALWAYS }
  | "Y"                     { YESTERDAY }
  | "O"                     { ONCE }
  | "H"                     { HISTORICALLY }
  (* | "~"                     { TILDE } *)
  | "->" | "=>"             { ARROW }
  | "<->" | "<=>"           { DARROW }
  | "&&"                    { AND }
  | "||"                    { OR }
  | '"'                     { read_string (Buffer.create 17) lexbuf }
  | lid as lid              { LID lid }
  | uid as uid              { UID uid }
  (* | "_"                     { UNDERSCORE }     *)  
  | newline                 { next_line lexbuf; tokenize lexbuf }
  | eof                     { EOF }
  | _ as char               { raise (Lexical_error (pos_range lexbuf, Format.sprintf "Unexpected character '%s'" (Char.escaped char))) }
and read_single_line_comment = parse
  | newline { next_line lexbuf; tokenize lexbuf } 
  | eof { EOF }
  | _ { read_single_line_comment lexbuf } 
and read_multi_line_comment = parse
  | "*/" { tokenize lexbuf } 
  | newline { next_line lexbuf; read_multi_line_comment lexbuf } 
  | eof { raise (Syntax_error (pos_range lexbuf, "Lexer - Unexpected EOF - please terminate your comment.")) }
  | _ { read_multi_line_comment lexbuf } 
and read_string buf = parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (Lexical_error (pos_range lexbuf, "Illegal string character: " ^ Lexing.lexeme lexbuf )) }
  | eof { raise (Lexical_error (pos_range lexbuf, "String is not terminated")) }