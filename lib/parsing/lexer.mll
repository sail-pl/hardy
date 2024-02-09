{
  open Tokens

  exception Lexical_error of string
    let line_num = ref 1
}


let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let id = letter (letter|digit|'_')*

rule tokenize = parse
  | [' ' '\t' '\n' '\r']  { tokenize lexbuf }  (* Skip whitespaces *)
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
  | "=="                  { EQ }
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
  | eof                   { EOF }
  | _ as char            { raise (Lexical_error (Printf.sprintf "Unexpected character '%s' at line %d" (Char.escaped char) !line_num)) }
