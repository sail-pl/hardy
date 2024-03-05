%{
    open ArduinoSyntax.Automaton
%}

%token<string> ATOM 
%token<string> LABEL
%token TRUE FALSE
%token LBRACE RBRACE
%token NEVER AND OR ARROW GOTO  NOT IF  FI LPAREN RPAREN SEMI COLON  
%token EOF

%left OR
%left AND
%right NOT

%start <buchi_automaton> automaton

%%

let automaton := NEVER; LBRACE ; states = state* ; RBRACE ; EOF ; { List.fold_left (fun (states,trans) (s,t) -> (s::states, t@trans)) ([],[]) states }

let state := l = LABEL ; COLON ; IF ; tr = transition* ; FI ; SEMI ;  { l,List.map (fun t -> t l) tr}

let transition := COLON ; COLON ; f = bform ; ARROW ; GOTO ; s2 = LABEL ; { fun s1 ->  (s1,f,s2) }

let bform := 
    | ~ = ATOM ; <Atom>
    | TRUE ; {True}
    | FALSE ; {False}
    | f1 = bform ; AND ; f2 = bform ; { And (f1,f2) }
    | f1 = bform ; OR ; f2 = bform ; { Or (f1,f2) }
    | ~ = preceded(NOT, bform) ; <Not>
    | ~ = delimited(LPAREN, bform, RPAREN) ; <>

