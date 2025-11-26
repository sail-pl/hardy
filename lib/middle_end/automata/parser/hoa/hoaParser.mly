%{
    open SyntaxCommon
    open HoaSyntax
%}

// based on https://adl.github.io/hoaf/

%token<string> STRING 
%token<int> INT 
%token<bool> BOOL
%token<string> ID 
%token<string> ANAME 
%token<string> HEADERNAME 

%token BEGIN END ABORT
%token HOA STATES STATE START AP ALIAS ACCEPTANCE ACC_NAME TOOL NAME PROPS ACCEPT_INF ACCEPT_FIN

%token AMPER BANG LPAR RPAR BAR LBRACE RBRACE LSQBRACE RSQBRACE


// %token LBRACE RBRACE
%token EOF

%left BAR
%left AMPER
%right BANG

%start <hoa> automaton

%%


let automaton := can_abort(header=header ; BEGIN; body=body ; END ; EOF ; { {header;body} })


// hoa is designed to be parsed as a continuous stream. after reading abort, it is allowed that a new automaton definition follows.
let can_abort(rules) == r=rules ; <> |  ABORT ; ~=automaton ; <> 


let header := version=format_version ; items=header_item* ; { {version;items} }

let format_version := HOA ; ~=ID ; <>

let header_item := 
    | STATES ; ~=INT ; <States>
    | START ; ~=state_conj ; <Start>
    | AP ; ~=INT ; ~=STRING* ; <Atomic>
    | ALIAS ; ~=ANAME ; ~=label_expr ; <Alias>
    | ACCEPTANCE ; ~=INT ; ~=acceptance_cond ; <Accept>
    | ACC_NAME ; ~=ID ; ~=midrule(~=ID ; <Either.Left> | ~=INT; <Either.Right>)* ; <AcceptName>
    | TOOL ; ~=STRING ; ~=STRING? ; <Tool>
    | NAME ; ~=STRING ; <Name>
    | PROPS ; ~=ID* ; <Properties>
    | HEADERNAME ; ~=midrule(~=BOOL; <AnyBool> | ~=INT; <AnyInt>| ~=STRING; <AnyString> | ~=ID ; <AnyId>)* ; <Other> 

let state_conj == separated_nonempty_list(AMPER,INT)

let label_expr :=
    | ~=BOOL ; <BoolLabel>
    | ~=INT ; <IntLabel>
    | ~=ANAME ; <NameLabel>

let eba :=     
    | ~ = label_expr ; <Atom>
    | BANG ; ~=eba ; <Not>
    | LPAR ; ~=eba ; RPAR ; <>
    | e1=eba ; AMPER ; e2=eba ; {And (e1,e2)}
    | e1=eba ; BAR ; e2=eba ; {Or (e1,e2)}

let acceptance_cond :=
    | ACCEPT_FIN ; LPAR ; complement=boption(BANG) ; set_number=INT ; RPAR ; { SetCond {fin_occur=true; set_number; complement } }
    | ACCEPT_INF ; LPAR ; complement=boption(BANG) ; set_number=INT ; RPAR ; { SetCond {fin_occur=false; set_number; complement } }
    | LPAR ; ~=acceptance_cond ; RPAR ; <>
    | c1=acceptance_cond ; AMPER ; c2=acceptance_cond ; {ConjAccept (c1,c2)}
    | c1=acceptance_cond ; BAR ; c2=acceptance_cond ; {DisjAccept (c1,c2)}
    | ~=BOOL ; <BoolAccept>

let body := ~=midrule(~=state_name ; ~=edge* ; <>)* ; <>

let state_name := STATE ; state_label=label? ; state_number=INT ; state_name=STRING? ; state_acc_sets=loption(acc_sig) ; { {state_number; state_label; state_name; state_acc_sets} }

let acc_sig := LBRACE ; ~=INT* ; RBRACE ; <>

let edge := edge_label=label? ; edge_dst=state_conj ; edge_acc_sets=loption(acc_sig) ; { {edge_dst; edge_label; edge_acc_sets} } 

let label := LSQBRACE ; ~=eba ; RSQBRACE ; <>