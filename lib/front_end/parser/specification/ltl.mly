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
        | ~ = atom ; <LTL_Atom>
        | ~ = unary_top ; ~ = ltl(atom) ; %prec UNARY <LTL_Unary>
        | ~ = midrule(~ = common_logic_unary ; <LTL_StdUnary>) ; ~ = ltl(atom) ; %prec UNARY <LTL_Unary>
        | ~ = ltl(atom) ; ~ = binary_top ; ~ = ltl(atom) ; <LTL_Binary>
        | ~ = ltl(atom) ; ~ = endrule(~ = common_logic_binary ; <LTL_StdBinary>) ; ~ = ltl(atom) ; <LTL_Binary>
    )
    | ~ = delimited("(",ltl(atom),")") ; <>



let unary_top == 
    | EVENTUALLY ; {Eventually}
    | ALWAYS ; {Always}
    | NEXT ; {Next}

let binary_top == 
    | SRELEASE ; {StrongRelease}
    | RELEASE ; {Release}
    | WEAK_UNTIL ; {WeakUntil}
    | UNTIL ; {Until}
