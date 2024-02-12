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
let letter = ['a'-'z' 'A'-'Z']
let id = letter (letter|digit|'_')*
let newline = '\r' | '\n' | "\r\n"

rule tokenize = parse
  | [' ' '\t']  { tokenize lexbuf }  (* Skip whitespaces *)
  | "true" { LTRUE }
  | "false" { LFALSE }
  | "if"                  { IF }
  | "then"                  {THEN}
  | "else"                { ELSE }
  | "while"               { WHILE }
  | "do"                    {DO}
  | "end"               {END}
  | "done"              {DONE}
  | "setup"                 {SETUP}
  | "loop"                  {LOOP}
  | "var"                   { VAR }
  | "input"                 {INPUT}
  | "output"                {OUTPUT}
  | "requires"              {REQUIRES}
  | "ensures"             {ENSURES}
  | "invariant"           {INVARIANT}
  | "variant"           {VARIANT}
  | "forall"                {FORALL}
  | "exists"                {EXISTS}
  | "("                   { LPAREN }
  | ")"                   { RPAREN }
  | "{"                     {LBRACE}
  | "}"                     {RBRACE}
  | ";"                   { SEMI }
  | ":="                   { ASSIGN }
  | "emit"                  { EMIT }
  | "!"                     {READ}
  | "+"                   { PLUS }
  | "-"                   { MINUS }
  | "*"                   { TIMES }
  | "/"                   { DIVIDE }
  | "="                  { EQ }
  | ">"                   { GT }
  | "<"                   { LT }
  | ">="                  { GTE }
  | "<="                  { LTE }
  | "True"                { TRUE }
  | "False"                { FALSE }
  | ";"                     {SEMI}
  | ":"                     {COLON}
  | ","                     {COMMA}
  | "S"                     {SINCE}
  | "Y"                     {YESTERDAY}
  | "O"                     {ONCE}
  | "H"                     {HISTORICALLY}
  | "Not"                   {NOT}
  | "->"                   {ARROW}
  | "/\\"                    {AND}
  | "\\/"                    {OR}
  | id as lxm            { ID (lxm) }
  | digit+ as lxm        { INT (int_of_string lxm) }
  | newline { next_line lexbuf; tokenize lexbuf }
  | eof                   { EOF }
  | _ as char            { raise (Lexical_error (pos_range lexbuf, Printf.sprintf "Unexpected character '%s'" (Char.escaped char))) }
