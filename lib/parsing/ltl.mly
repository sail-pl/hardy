

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
    | WNEXT ; {WeakNext}
    | ~ = common_logic_unary ; <LTL_UArithm>


let binary == 
    | SRELEASE ; {StrongRelease}
    | RELEASE ; {Release}
    | WUNTIL ; {WeakUntil}
    | UNTIL ; {Until}
    | ~ = common_logic_binary ; <LTL_BArithm>


%public
let requires == ~ = preceded(RELY, braced_ltl) ; <LTL>

%public
let prog_ensures == ~ = preceded(GUARANTEE, braced_ltl) ; <LTL>

%public
let setup_ensures == ~ = preceded(ENSURES, braced_fol) ;  <FOL>

let braced_ltl == f = braced(ltl?) ; {Option.value f ~default:{value=LTL_True;loc=Some $loc}}
let braced_fol == f = braced(fol?) ; {Option.value f ~default:{value=FOL_True;loc=Some $loc}}