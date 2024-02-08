%token <int> INT
%token <string> ID

%token PLUS "+" MINUS "-" TIMES "*" DIVIDE "/" LPAREN "(" RPAREN ")"  
%token EQ "==" GT ">" LT "<" GTE ">=" LTE "<=" LTRUE LFALSE
%token FORALL EXISTS IMP AND OR TRUE FALSE NOT COMMA ","
%token EOF

// IMP BASE
%token IF "if" THEN "then"
%token ELSE "else" WHILE "while" DO "do" DONE "done" END "end" ASSIGN ":=" SEMI ";" COLON ":" 

%token SETUP LOOP 
%token EMIT READ VAR INPUT OUTPUT REQUIRES ENSURES INVARIANT VARIANT LBRACE "{" RBRACE "}"

%token YESTERDAY SINCE ONCE HISTORICALLY


%left PLUS MINUS 
%left TIMES DIVIDE 
%left AND OR IMP

%nonassoc EQ GT LT GTE LTE 
%nonassoc UNARY
%nonassoc COMMA

%%