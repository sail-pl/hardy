%{
    open LTLSyntax
    open FOLSyntax
    open InstantSyntax
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
let tq_expr == expr(
    | id = ID ; {id,None}
    | id = ID ; endrule(AT|SYMB_AT) ; n = INT ; {id,Some (At n)}
    | endrule(PREV | LAST) ; n = endrule(n = option(INT); {Option.value ~default:1 n}) ; id = ID ;  {id,Some (Previous n)}
    | id = ID ; SHARP ; n = INT ; {id,Some (Previous n)}
    | endrule(START | FIRST | DOLLAR) ; id = ID ;  {id,Some (At 0)}
)


%public
let inst_spec == braced(fol)

%public
let prog_requires == delimited(RELY, ltl, ".")

%public
let prog_ensures == delimited(GUARANTEE, ltl, ".") 

%public
let state_requires == preceded(REQUIRES, inst_spec)

%public
let state_ensures == preceded(ENSURES, inst_spec) 