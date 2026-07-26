%start <(Ppltl_spec.parsed_temp_spec_t, unit, Ppltl_spec.parsed_spec_t, unit, LoopySyntax.parsed_env) LoopySyntax.program> program

%%

%public
let inst_spec == braced(fol(spec_expr_with_pred))
%public
let temporal_spec == ltl(braced(pltl(braced(fol(spec_expr_with_pred)))))
