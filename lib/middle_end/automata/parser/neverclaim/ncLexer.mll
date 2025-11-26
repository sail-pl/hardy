{
  open Lexing
  open NcParser

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
let acc_label = "accept_" (letter|digit)+ 
let nacc_label = 'T' digit+ '_' letter+ digit*
let atom = "f_" ['1' - '9'] digit* 
let newline = '\r' | '\n' | "\r\n"


rule tokenize = parse
    | [' ' '\t']              { tokenize lexbuf }  (* Skip whitespaces *)
    | "/*"                     {ignore_comment lexbuf}
    | "never"                 { NEVER }
    | '1'                      { TRUE } 
    | "true"                     { NC_TRUE } 
    | '0'                      { FALSE } 
    | "false"                   {NC_FALSE}
    | "&&"                     { AND }
    | "||"                     { OR }
    | "->"                     { ARROW }
    | "goto"                     { GOTO }
    | "!"                     { NOT }
    | "if"                    { IF }
    | "fi"                    { FI }
    | "("                     { LPAREN }
    | ")"                     { RPAREN }
    | "{"                     { LBRACE }
    | "}"                     { RBRACE }
    | ";"                     { SEMI }
    | ";"                     { SEMI }
    | ":"                     { COLON }
    | "skip"                  { SKIP }
    | acc_label 
    | nacc_label as lbl       { LABEL (lbl) }
    | atom as atm             { ATOM (atm) }
    | newline                 { next_line lexbuf; tokenize lexbuf }
    | eof                     { EOF }
    | _ as char               { failwith @@ Format.sprintf "Unexpected character '%s'" (Char.escaped char) }
    and ignore_comment = parse
    | "*/"                    { tokenize lexbuf }
    | newline                 { next_line lexbuf; ignore_comment lexbuf }
    | _                       { ignore_comment lexbuf }
