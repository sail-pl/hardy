%{
    open Loopy
    open Ppltl
%}

%start <(Spec.parsed_temp_spec_t, unit, (Spec.parsed_spec_t, unit, Syntax.parsed_env) program) prog_with_spec> program

%%

%public
let inst_spec == braced(fol(spec_expr_with_pred))
%public
let temporal_spec == ltl(braced(pltl(braced(fol(spec_expr_with_pred)))))
