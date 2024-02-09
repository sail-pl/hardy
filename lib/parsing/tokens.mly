%token <int> INT
%token <string> ID

// EXP & LOGIC
%token PLUS "+" MINUS "-" TIMES "*" DIVIDE "/" 
%token EQ "==" GT ">" LT "<" GTE ">=" LTE "<=" LTRUE LFALSE

// LOGIC
%token FORALL EXISTS ARROW AND OR TRUE FALSE NOT 
%token EOF

// IMP 
%token IF "if" THEN "then"
%token ELSE "else" WHILE "while" DO "do" DONE "done" END "end" ASSIGN ":="

// REACTIVE
%token SETUP LOOP EMIT READ VAR INPUT OUTPUT 

// SPEC
%token REQUIRES ENSURES INVARIANT VARIANT 

// PLTL
%token YESTERDAY SINCE ONCE HISTORICALLY

// MISC
%token SEMI ";" COLON ":" LPAREN "(" RPAREN ")" LBRACE "{" RBRACE "}" COMMA ","


// ASSOC
%right SINCE
%nonassoc NOT YESTERDAY ONCE HISTORICALLY

%right ARROW
%right OR
%right AND
%left PLUS MINUS
%left TIMES DIVIDE

%nonassoc EQ GT LT GTE LTE 
%nonassoc COMMA

%%