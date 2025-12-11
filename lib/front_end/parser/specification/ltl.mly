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
        | ~ = unary ; ~ = ltl(atom) ; %prec UNARY <LTL_Unary>
        | f1 = ltl(atom) ; op = binary ; f2 = ltl(atom) ; {LTL_Binary (f1,op,f2)}
        | ~ = atom ; <LTL_Atom>
    )
    | ~ = delimited("(",ltl(atom),")") ; <>



let unary == 
    | EVENTUALLY ; {Eventually}
    | ALWAYS ; {Always}
    | NEXT ; {Next}
    | ~ = common_logic_unary ; <LTL_StdUnary>

let binary == 
    | SRELEASE ; {StrongRelease}
    | RELEASE ; {Release}
    | WUNTIL ; {WeakUntil}
    | UNTIL ; {Until}
    | ~ = common_logic_binary ; <LTL_StdBinary>