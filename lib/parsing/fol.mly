%%

%public
let requires == preceded(REQUIRES, braced_fol)

%public
let prog_ensures == preceded(ENSURES, braced_fol)

%public
let setup_ensures == prog_ensures