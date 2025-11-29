{
  open Tokens
  open Lexing

  exception Lexical_error of (position * position) * string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                pos_lnum = pos.pos_lnum + 1
      }

  let pos_range lexbuf = 
    let sp = lexeme_start_p lexbuf and ep = lexeme_end_p lexbuf in 
    sp,ep

let remove_leading_plus s =
  let n = String.length s in
  if n > 0 && s.[0] = '+' then String.sub s 1 (n-1) else s

}


let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']
let letter = (lowercase | uppercase)
let nameStartChar = lowercase | '_'
let nameChar = nameStartChar | digit
let name = nameStartChar (nameChar)*
let id = lowercase (letter|digit|'_')* (* cannot begin with an uppercase because of reserved LTL keywords *)
let newline = '\r' | '\n' | "\r\n"



rule tokenize = parse
  | [' ' '\t']              { tokenize lexbuf }  (* Skip whitespaces *)
  | "//"                    { read_comment lexbuf } (* single-line comment *)
  | "unit"                  { TY_UNIT }
  | "bool"                  { TY_BOOL }
  | "int"                   { TY_INT } 
  | "real"                  { TY_REAL }
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
  | "setup"                 { SETUP }
  | "loop"                  { LOOP }
  | "var"                   { VAR }
  | "input"                 { INPUT }
  | "output"                { OUTPUT }
  | "relies on"             { RELY }
  | "guarantees"            { GUARANTEE }
  (* | "requires"              { REQUIRES } *)
  | "prev"                  { PREV }
  (* | "^"                     { HAT } *)
  (* | "any"                   { ANY } *)
  (* | "?"                     { QMARK } *)
  (* | "all"                   { ALL } *)
  | "#"                     { SHARP }
  | "$"                     { DOLLAR }
  | "at"                    { AT }
  | "as"                    { AS }
  | "@"                     { SYMB_AT }
  | "last"                  { LAST }
  | "first"                 { FIRST }
  | "start"                 { START }
  | "ensures"               { ENSURES }
  | "invariant"             { INVARIANT }
  | "variant"               { VARIANT }
  | "forall"                { FORALL }
  | "forall_prev"           { FORALL_PREV }
  | "exists_prev"           { EXISTS_PREV }
  | "exists"                { EXISTS }
  | "("                     { LPAREN }
  | ")"                     { RPAREN }
  | "{"                     { LBRACE }
  | "}"                     { RBRACE }
  | "["                     { LSQBRACE }
  | "]"                     { RSQBRACE }
  | "|"                     { SEP }
  | ";"                     { SEMI }
  | ":="                    { ASSIGN }
  | "emit"                  { EMIT }
  | "to"                    { TO }
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
  (* | "~"                     { TILDE } *)
  | "->" | "=>"             { ARROW }
  | "<->" | "<=>"           { DARROW }
  | "&&"                    { AND }
  | "||"                    { OR }
  | '"'                     { read_string (Buffer.create 17) lexbuf }
  | digit+ as lxm           { INT (int_of_string lxm) }
  
  (* from https://gitlab.inria.fr/why3/why3/-/blob/master/src/parser/lexer.mll#L98 *)
  | (digit+ as i)     ("" as f)    ['e' 'E'] (['-' '+']? digit+ as e)
  | (digit+ as i) '.' (digit* as f) (['e' 'E'] (['-' '+']? digit+ as e))?
  | (digit* as i) '.' (digit+ as f) (['e' 'E'] (['-' '+']? digit+ as e))?
       { REAL (~radix:10,~num:i,~frac:f,~exp:(Option.map remove_leading_plus e))}
  | id as lxm               { ID (lxm) }
  | newline                 { next_line lexbuf; tokenize lexbuf }
  | eof                     { EOF }
  | _ as char               { raise (Lexical_error (pos_range lexbuf, Format.sprintf "Unexpected character '%s'" (Char.escaped char))) }
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
and read_comment = parse
  | newline { next_line lexbuf; tokenize lexbuf } 
  | eof { EOF }
  | _ { read_comment lexbuf } 