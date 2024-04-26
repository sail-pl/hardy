%{
    open HardySyntax.PromelaSyntax
%}

%token<string> ATOM 
%token<string> LABEL
%token TRUE FALSE
%token LBRACE RBRACE
%token NEVER AND OR ARROW GOTO  NOT IF  FI LPAREN RPAREN SEMI COLON SKIP
%token EOF

%left OR
%left AND
%right NOT

%start <neverclaim> automaton

%%

let automaton := NEVER; LBRACE ; states = state* ; RBRACE ; EOF ; { 
    let slist, tlist = List.fold_left (fun (states,trans) (s,t) -> ({pml_state=s}::states, t@trans)) ([],[]) states 
    in {pml_states = slist; pml_transitions=tlist}
    }

let state := l = LABEL ; COLON ; 
    content = midrule(
        (* SKIP is used when the last state accepts everything, so we have a transition labeled true to itself *)
        | SKIP ; {fun l -> (l, [{pml_src={pml_state=l};pml_form=True;pml_dst={pml_state=l}}])}
        | IF ; tr = transition* ; FI ; SEMI ; { fun l -> (l,List.map (fun t -> t l) tr)} 
    ); {content l}

let transition := COLON ; COLON ; f = bform ; ARROW ; GOTO ; s2 = LABEL ; { fun s1 ->  {pml_src={pml_state=s1};pml_form=f;pml_dst={pml_state=s2}} }

let bform := 
    | ~ = ATOM ; <Atom>
    | TRUE ; {True}
    | FALSE ; {False}
    | f1 = bform ; AND ; f2 = bform ; { And (f1,f2) }
    | f1 = bform ; OR ; f2 = bform ; { Or (f1,f2) }
    | ~ = preceded(NOT, bform) ; <Not>
    | ~ = delimited(LPAREN, bform, RPAREN) ; <>

