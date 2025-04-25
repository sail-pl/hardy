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

}


let digit = ['0'-'9']
let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']
let letter = (lowercase | uppercase)
let nameStartChar = lowercase | '_'
let nameChar = nameStartChar | digit
let name = nameStartChar (nameChar)*
let id = letter (lowercase|digit|'_')* (* no uppercase because of reserved LTL keywords *)
let newline = '\r' | '\n' | "\r\n"


rule tokenize = parse
  | [' ' '\t']              { tokenize lexbuf }  (* Skip whitespaces *)
  | "//"                    { read_comment lexbuf } (* single-line comment *)
  | "bool"                  { TY_BOOL }
  | "int"                   { TY_INT } 
  | "true"                  { LTRUE  } 
  | "false"                 { LFALSE }
  | "if"                    { IF }
  | "then"                  { THEN }
  | "else"                  { ELSE }
  | "while"                 { WHILE }
  | "do"                    { DO  }
  | "end"                   { END }
  | "done"                  { DONE }
  | "WHEN"                  { WHEN }
  | "GOTO"                  { GOTO }
  | "var"                   { VAR }
  | "local"                 { LOCAL }
  | "input"                 { INPUT }
  | "output"                { OUTPUT }
  | "relies on"             { RELY }
  | "guarantees"            { GUARANTEE }
  | "requires"              { REQUIRES }
  | "prev"                  { PREV }
  | "^"                     { HAT }
  | "any"                   { ANY }
  | "?"                     { QMARK }
  | "all"                   { ALL }
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
  | "exists_prev"           { EXISTS_PREV }
  | "exists"                { EXISTS }
  | "("                     { LPAREN }
  | ")"                     { RPAREN }
  | "{"                     { LBRACE }
  | "}"                     { RBRACE }
  | "["                     { LSQBRACE }
  | "]"                     { RSQBRACE }
  (* | "|"                     { SEP } *)
  | ";"                     { SEMI }
  | ":="                    { ASSIGN }
  | "emit"                  { EMIT }
  | "to"                    { TO }
  | "."                     { DOT }
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
  | "S"                     { SINCE }
  | "X"                     { NEXT }
  | "U"                     { UNTIL}
  | "R" | "V"               { RELEASE }
  | "M"                     { SRELEASE }
  | "F"                     { EVENTUALLY }
  | "G"                     { ALWAYS }
  | "~"                     { TILDE }
  | "->" | "=>"             { ARROW }
  | "<->" | "<=>"           { DARROW }
  | "&&"                    { AND }
  | "||"                    { OR }
  | digit+ as lxm           { INT (int_of_string lxm) }
  | id as lxm               { ID (lxm) }
  | uppercase+ as state_id     { STATE state_id }
  | newline                 { next_line lexbuf; tokenize lexbuf }
  | eof                     { EOF }
  | _ as char               { raise (Lexical_error (pos_range lexbuf, Printf.sprintf "Unexpected character '%s'" (Char.escaped char))) }
and read_comment = parse
  | newline { next_line lexbuf; tokenize lexbuf } 
  | eof { EOF }
  | _ { read_comment lexbuf } 