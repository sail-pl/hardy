%start <(Pltl_spec.parsed_temp_spec_t, unit, Pltl_spec.parsed_spec_t, unit, ProgramSyntax.parsed_env) ProgramSyntax.program> program

%%

%public
let inst_spec == fol(braced(expr_with_pred))
%public
let temporal_spec == ltl(braced(pltl(braced(inst_spec))))
