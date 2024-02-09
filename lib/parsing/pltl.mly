%%

%public
let pltl :=
    | TRUE ; {PLTL_True}
    | unary(pltl)
    | f1 = pltl ; OR ; f2 = pltl ; <PLTL_Or>
    | f1 = pltl ; SINCE ; f2 = pltl ; <Since>



let unary(f) == 
    | ~ = preceded(NOT,f) ; <PLTL_Not>
    | ~ = preceded(ONCE,f) ; <Once>
    | ~ = preceded(HISTORICALLY,f) ; <Historically>
    | ~ = preceded(YESTERDAY,f) ; <Yesterday>


%public
let requires == ~ = preceded(REQUIRES, braced(pltl)) ; <PLTL>

%public
let ensures == ~ = preceded(ENSURES, braced(pltl)) ; <PLTL>