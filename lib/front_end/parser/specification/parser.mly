%{
    open LTLSyntax
    open FOLSyntax
%}

%%


let ltl := 
    | located(
        | TRUE ; {LTL_True} 
        | FALSE ; {LTL_False}
        | ~ = unary ; ~ = ltl ; <LTL_Unary>
        | f1 = ltl ; op = binary ; f2 = ltl ; {LTL_Binary (f1,op,f2)}
        | ~ = braced(fol) ; <LTL_Pred> // can't use () because fol includes expr 
    )
    | ~ = delimited("(",ltl,")") ; <>



let unary == 
    | EVENTUALLY ; {Eventually}
    | ALWAYS ; {Always}
    | NEXT ; {Next}
    | ~ = common_logic_unary ; <LTL_UArithm>


let binary == 
    | SRELEASE ; {StrongRelease}
    | RELEASE ; {Release}
    | WUNTIL ; {WeakUntil}
    | UNTIL ; {Until}
    | ~ = common_logic_binary ; <LTL_BArithm>


%public
let prog_requires == delimited(RELY, ltl, ".")

%public
let prog_ensures == delimited(GUARANTEE, ltl, ".") 

%public
let setup_ensures == preceded(ENSURES, braced(fol)) 
