%{
    open PpLTLSyntax
%}
%%




%public
let pltl(atom) := 
    | located(
        | TRUE ; {PLTL_True} 
        | FALSE ; {PLTL_False}
        | a = atom ; {PLTL_Atom (mk_labeled ~label:() a)}
        | ~ = unary_op ; ~ = pltl(atom) ; %prec UNARY <PLTL_Unary>
        | f1 = pltl(atom) ; op = binary_op ; f2 = pltl(atom) ; {PLTL_Binary (f1,op,f2)}
    )
    | "(" ; ~ = pltl(atom) ; ")" ; <>



let unary_op == 
    | ONCE ; {Once}
    | YESTERDAY; {Yesterday}
    | WEAK_YESTERDAY; {WeakYesterday}
    | HISTORICALLY ; { Historically }
    | ~ = common_logic_unary ; <PLTL_StdUnary>


let binary_op == 
    | SINCE ; {Since}
    | WEAK_SINCE ; { WeakSince }
    | ~ = common_logic_binary ; <PLTL_StdBinary>