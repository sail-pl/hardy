%%

%public
let requires == ~ = preceded(REQUIRES, braced_fol) ; <FOL>

%public
let prog_ensures == ~ = preceded(ENSURES, braced_fol) ; <FOL>

%public
let setup_ensures == prog_ensures

let braced_fol == f = braced(fol?) ; {Option.value f ~default:{value=FOL_True;loc=Some $loc}}