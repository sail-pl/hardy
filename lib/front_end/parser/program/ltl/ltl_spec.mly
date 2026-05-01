%{
    open InstantSyntax
    open FOLSyntax

%}


%start <(Ltl_spec.parsed_temp_spec_t, unit, Ltl_spec.parsed_spec_t, unit, ProgramSyntax.parsed_env) ProgramSyntax.program> program

%%

%public
let tq_expr := spec_expr(
    | id = ID ; {id,None}
    | id = ID ; endrule(AT|SYMB_AT) ; n = INT ; {id,Some (At n)}
    | endrule(PREV | LAST) ; n = endrule(n = option(INT); {Option.value ~default:1 n}) ; id = ID ;  {id,Some (Previous n)}
    | id = ID ; SHARP ; n = INT ; {id,Some (Previous n)}
    | endrule(START | FIRST | DOLLAR) ; id = ID ;  {id,Some (At 0)}
)

%public
let tq_expr_with_pred == 
    | ~=tq_expr ; <Atom> 
    // | name = ID ; args=loption(delimited("(",separated_list(COMMA, tq_expr),")")) ; { Predicate {name;args} } 


let fol_h(atom) ==
    located(
    | FORALL_PREV ; h_var = ID; AS ; binder = ID; COMMA ; f = fol(atom) ; {ForallPrev {h_var;binder;f}}
    | EXISTS_PREV ; h_var = ID; AS ; binder = ID; COMMA ; f = fol(atom) ; {ExistsPrev {h_var;binder;f}}
    )
    | fol(atom)


%public
let inst_spec == braced(fol(spec_expr_with_pred))
%public
let temporal_spec == ltl(braced(fol_h(tq_expr_with_pred)))
