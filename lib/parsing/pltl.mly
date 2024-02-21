%%


let pltl := 
    | located(
        | TRUE ; {PLTL_True} 
        | FALSE ; {PLTL_False}
        | ~ = delimited(LSQBRACE,fol,RSQBRACE) ; <PLTL_Pred> // can't use () because fol includes expr 
        | ~ = unary ; ~ = pltl ; <PLTL_Unary>
        | f1 = pltl ; op = binary ; f2 = pltl ; {PLTL_Binary (f1,op,f2)}
    )
    | "(" ; ~ = pltl ; ")" ; <>



let unary == 
    | ONCE ; {Once}
    | YESTERDAY; {Before}
    | HISTORICALLY ; { Historically }
    | ~ = common_logic_unary ; <PLTL_UArithm>


let binary == 
    | SINCE ; {Since}
    | ~ = common_logic_binary ; <PLTL_BArithm>


%public
let requires == 
    ~ = preceded(RELY, braced_pltl) ; <PLTL>

%public
let prog_ensures == ~ = preceded(GUARANTEE, braced_pltl) ; <PLTL>

%public
let setup_ensures == ~ = preceded(ENSURES, braced(fol)) ;  <FOL>



let braced_pltl == f = braced(pltl?) ; {Option.value f ~default:{value=PLTL_True;loc=Some $loc}}
