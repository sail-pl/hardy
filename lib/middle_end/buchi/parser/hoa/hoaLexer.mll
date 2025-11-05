{
  open Lexing
  open HoaParser

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


let identifier = (lowercase | uppercase|'_') (digit|lowercase|uppercase|'-'|'_')*

let int = '0'|['1'-'9']['0'-'9']*

let alias = '@'(digit|lowercase|uppercase|'-'|'_')+

let header = identifier ':'

let newline = '\r' | '\n' | "\r\n"

rule tokenize = parse
    | [' ' '\t']                  { tokenize lexbuf }  (* Skip whitespaces *)
    | "/*"                        { ignore_comment lexbuf}
    | "--BODY--"                  { BEGIN }
    | "--END--"                   { END }
    | "--ABORT--"                 { ABORT }
    | "HOA:"                      { HOA }
    | "States:"                   { STATES }
    | "State:"                    { STATE }
    | "Start:"                    { START }
    | "AP:"                       { AP }
    | "Alias:"                    { ALIAS }
    | "Acceptance:"               { ACCEPTANCE }
    | "acc-name:"                 { ACC_NAME }
    | "tool:"                     { TOOL }
    | "name:"                     { NAME }
    | "properties:"               { PROPS }
    | int as n                    { INT (int_of_string n) }
    | header  as h                { HEADERNAME (h) }
    | 't'                         { BOOL(true) } 
    | 'f'                         { BOOL(false) } 
    | '&'                         { AMPER }
    | '('                         { LPAR }
    | ')'                         { RPAR }
    | '{'                         { LBRACE }
    | '}'                         { RBRACE }
    | '['                         { LSQBRACE }
    | ']'                         { RSQBRACE }
    | '!'                         { BANG }
    | '|'                         { BAR }
    | "Fin"                       { ACCEPT_FIN }
    | "Inf"                       { ACCEPT_INF }
    | identifier as id            { ID (id ) }
    | alias as a                  { ANAME (a) } 
    | newline                     { next_line lexbuf; tokenize lexbuf }
    | '"'                         { read_string ( Buffer.create 17) lexbuf }
    | eof                         { EOF }
    | _ as char                   { failwith @@ Format.sprintf "Unexpected character '%s'" (Char.escaped char) }
    and ignore_comment = parse    
    | "*/"                        { tokenize lexbuf }
    | newline                     { next_line lexbuf; ignore_comment lexbuf }
    | _                           { ignore_comment lexbuf }
    and read_string buf = parse
    | '"'                         { STRING (Buffer.contents buf) }
    | '\\' '/'                    { Buffer.add_char buf '/'; read_string buf lexbuf }
    | '\\' '\\'                   { Buffer.add_char buf '\\'; read_string buf lexbuf }
    | '\\' 'b'                    { Buffer.add_char buf '\b'; read_string buf lexbuf }
    | '\\' 'f'                    { Buffer.add_char buf '\012'; read_string buf lexbuf }
    | '\\' 'r'                    { Buffer.add_char buf '\r'; read_string buf lexbuf }
    | '\\' 'n'                    { Buffer.add_char buf '\n'; read_string buf lexbuf }
    | '\\' 't'                    { Buffer.add_char buf '\t'; read_string buf lexbuf }
    | [^ '"' '\\']+               { Buffer.add_string buf (Lexing.lexeme lexbuf);  read_string buf lexbuf  }
    | _                           { failwith @@ Format.sprintf  "Illegal string character: " ^ Lexing.lexeme lexbuf }
    | eof                         { failwith @@ Format.sprintf "String is not terminated" }