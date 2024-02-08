%%

%public
let requires == ~ = preceded(REQUIRES, braced(fol)) ; <FOL>

%public
let ensures == ~ = preceded(ENSURES, braced(fol)) ; <FOL>