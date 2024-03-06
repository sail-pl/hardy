%%


let ltl := 
    | located(
        | TRUE ; {LTL_True} 
        | FALSE ; {LTL_False}
        | ~ = unary ; ~ = ltl ; <LTL_Unary>
        | f1 = ltl ; op = binary ; f2 = ltl ; {LTL_Binary (f1,op,f2)}
        | ~ = delimited(LSQBRACE,fol,RSQBRACE) ; <LTL_Pred> // can't use () because fol includes expr 
    )
    | "(" ; ~ = ltl ; ")" ; <>



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
let requires == f = preceded(RELY, braced_ltl)? ; {Option.join f}

%public
let prog_ensures == f = preceded(GUARANTEE, braced_ltl)? ; {Option.join f}

%public
let setup_ensures == f = preceded(ENSURES, braced_fol)? ; {Option.join f}

let braced_ltl == f = braced(ltl?) ; { f }