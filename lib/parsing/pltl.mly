%%

%public
let pltl :=
    | TRUE ; {PLTL_True}
    | unary(pltl) 
    | f1 = pltl ; op = binary ; f2 = pltl ; {op f1 f2}


// todo stratify grammar 

let unary(f) == 
    | NOT ; ~ = f ; %prec UNARY <PLTL_Not>
    | ONCE ; ~ = f ; %prec UNARY <Once>
    | HISTORICALLY ; ~ = f ; %prec UNARY <Historically>
    | YESTERDAY ; ~ = f ; %prec UNARY  <Yesterday>


let binary == 
    | OR ; {fun x y -> PLTL_Or (x,y)}
    | SINCE ; {fun x y -> Since (x,y) }

%public
let requires == ~ = preceded(REQUIRES, braced(pltl)) ; <PLTL>

%public
let ensures == ~ = preceded(ENSURES, braced(pltl)) ; <PLTL>