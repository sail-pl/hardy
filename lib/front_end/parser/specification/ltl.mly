%{
    open LTLSyntax
    open FOLSyntax
%}

%%

%public 
let ltl(atom) := 
    | located(
        | TRUE ; {LTL_True} 
        | FALSE ; {LTL_False}
        | ~ = unary_top ; ~ = atom ; <LTL_Unary>
        | ~ = common_logic_unary ; ~ = ltl(atom) ; %prec UNARY <LTL_StdUnary>
        | f1 = atom ; op = binary_top ; f2 = atom ; {LTL_Binary (f1,op,f2)}
        | f1 = ltl(atom) ; op = common_logic_binary ; f2 = ltl(atom) ; {LTL_StdBinary (f1,op,f2)}
        | ~ = atom ; <LTL_Atom> 
    )
    | ~ = delimited("(",ltl(atom),")") ; <>



let unary_top == 
    | EVENTUALLY ; {Eventually}
    | ALWAYS ; {Always}
    | NEXT ; {Next}

let binary_top == 
    | SRELEASE ; {StrongRelease}
    | RELEASE ; {Release}
    | WUNTIL ; {WeakUntil}
    | UNTIL ; {Until}


%public
let tq_expr := expr(
    | id = LID ; {id,None}
    | id = LID ; endrule(AT|SYMB_AT) ; n = INT ; {id,Some (At n)}
    | endrule(PREV | LAST) ; n = endrule(n = option(INT); {Option.value ~default:1 n}) ; id = LID ;  {id,Some (Previous n)}
    | id = LID ; SHARP ; n = INT ; {id,Some (Previous n)}
    | endrule(START | FIRST | DOLLAR) ; id = LID ;  {id,Some (At 0)}
)

%public
let tq_expr_with_pred := 
    | ~=tq_expr ; <Atom> 
(*  | name = ID ; args=loption(delimited("(",separated_list(COMMA, tq_expr),")")) ; { Predicate {name;args} } *)


