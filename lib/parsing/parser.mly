%{
  open ArduinoSyntax.Syntax
%}

%token <int> INT
%token <string> ID
%token PLUS MINUS TIMES DIVIDE LPAREN RPAREN EQ GT LT GTE LTE IF THEN 
%token ELSE WHILE DO DONE END ASSIGN SEMI COLUMN SETUP LOOP EOF
%token EMIT READ VAR INPUT OUTPUT REQUIRES ENSURES INVARIANT VARIANT LBRACE RBRACE
%token FORALL EXISTS IMP AND OR TRUE FALSE NOT COMMA

%left PLUS MINUS
%left TIMES DIVIDE
%left AND OR IMP
%nonassoc EQ GT LT GTE LTE
%nonassoc UNARY
%nonassoc COMMA

%start <program> program

%%

program:
    | declaration requires ensures LOOP COLUMN invariant stmt_list EOF 
        {
            {
                prog_env = $1;
                prog_requires = $2;
                prog_ensures = $3;
                prog_setup = None; 
                prog_main = {main_invariant = $6; main_body = $7}
            }
        }
    | declaration requires ensures SETUP COLUMN ensures stmt_list LOOP COLUMN invariant stmt_list EOF 
        {{  prog_env = $1;
            prog_requires = $2;
            prog_ensures = $3;
            prog_setup = Some {setup_ensures = $6; setup_body = $7}; 
            prog_main = {main_invariant = $10; main_body = $11}
        }}

requires: 
    REQUIRES proposition {$2}

ensures :
    ENSURES proposition {$2}

invariant : 
    INVARIANT proposition {$2}

variant : 
    VARIANT LBRACE expr RBRACE {$3}

proposition :
    LBRACE formula RBRACE {$2}

declaration : 
    | input output var  {{env_input=$1;env_output=$2;env_variables=$3}}

var : 
    | {[]}
    | VAR id_list SEMI {$2}

input : 
    |  {[]}
    | INPUT id_list SEMI {$2}

output : 
    |   {[]}
    | OUTPUT id_list SEMI {$2}

formula :
    | TRUE {True}
    | FALSE {False}
    | expr {Pred $1}
    | NOT formula %prec UNARY {Not $2}
    | formula IMP formula {Imp ($1,$3)}
    | formula OR formula {Or ($1,$3)}
    | formula AND formula {And ($1,$3)}
    | FORALL ID COMMA formula {Forall($2,$4)} 
    | EXISTS ID COMMA formula {Exists($2,$4)} 

id_list:
  | id_list ID      { $1 @ [$2] }
  | ID                { [$1] }

stmt_list:
  | stmt_list stmt      { $1 @ [$2] }
  | stmt                { [$1] }

stmt:
  | ID ASSIGN expr SEMI  { Assign ($1, $3) }
  | ID EMIT expr SEMI  { Emit ($1, $3) }
| IF expr THEN stmt_list END { If ($2, $4, None) }
  | IF expr THEN stmt_list ELSE stmt_list END { If ($2, $4, Some $6) }
  | WHILE expr DO invariant variant stmt_list DONE { While ($2, $4, $5, $6) }
 
expr:
  | INT                 { Int $1 }
  | ID                  { Var $1 }
  | READ ID  {Read $2}
  | expr PLUS expr      { Add ($1, $3) }
  | expr MINUS expr     { Sub ($1, $3) }
  | expr TIMES expr     { Mul ($1, $3) }
  | expr DIVIDE expr    { Div ($1, $3) }
  | LPAREN expr RPAREN  { $2 }
  | expr EQ expr        { Eq ($1, $3) }
  | expr GT expr        { Gt ($1, $3) }
  | expr LT expr        { Lt ($1, $3) }
  | expr GTE expr       { Gte ($1, $3) }
  | expr LTE expr       { Lte ($1, $3) }