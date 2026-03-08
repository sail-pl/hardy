%token <int> INT
%token <(radix:int * num:string * frac:string * exp:string option)> REAL
%token <string> ID
%token <string> STRING

%token TY_INT TY_REAL TY_BOOL TY_STRING TY_ARRAY TY_UNIT

// EXP & LOGIC
%token EMARK SYMB_AT DOLLAR  SHARP UNDERSCORE HAT QMARK 
%token PLUS "+" MINUS "-" TIMES "*" DIVIDE "/" 
%token EQ "=" NEQ "<>" GT ">" LT "<" GTE ">=" LTE "<=" LTRUE LFALSE
%token LSQBRACE "[" RSQBRACE "]"

// LOGIC
%token AS EXISTS_PREV FORALL_PREV FORALL EXISTS ARROW DARROW AND OR TRUE FALSE
%token EOF

// IMP 
%token IF "if" THEN "then"
%token ELSE "else" WHILE "while" DO "do" DONE "done" END "end" ASSIGN ":="

// REACTIVE
%token SETUP LOOP EMIT TO VAR INPUT OUTPUT LAST FIRST START PREV AT ALL ANY 

// SPEC
%token ASSUMES GUARANTEES ENSURES INVARIANT VARIANT // REQUIRES 

// (P)LTL
%token YESTERDAY ONCE HISTORICALLY
%token EVENTUALLY ALWAYS NEXT UNTIL WUNTIL RELEASE SRELEASE
%token SINCE

// MISC
%token SEMI ";" COLON ":" LPAREN "(" RPAREN ")" LBRACE "{" RBRACE "}" COMMA ","  SEP "|" // DOT "."   TILDE "~"


// ASSOC
%nonassoc below_COMMA
%left COMMA
%right ARROW DARROW
%right OR
%right AND
%right EQ NEQ GT LT GTE LTE 
%left PLUS MINUS
%left TIMES DIVIDE
%right UNTIL WUNTIL SRELEASE RELEASE
%right SINCE
//%right EVENTUALLY ALWAYS
//%right NEXT
//%right ONCE HISTORICALLY
//%right YESTERDAY

%nonassoc UNARY //LPAREN
%%