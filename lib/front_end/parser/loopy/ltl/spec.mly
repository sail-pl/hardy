%{
    open Specification
    open InstantSyntax
    open FOLSyntax
    open Loopy
    open Ltl

%}


%start <(Spec.parsed_temp_spec_t, unit, (Spec.parsed_spec_t, unit, Syntax.parsed_env) Syntax.program) prog_with_spec> program

%%

%public
let tq_expr := spec_expr(
    | id = LID ; {id,None}
    | id = LID ; endrule(AT|SYMB_AT) ; n = INT ; {id,Some (At n)}
    | id = LID ; endrule(AT|SYMB_AT) ; id_binder = LID ; {id,Some (Same id_binder)}
    | endrule(PREV | LAST) ; n = endrule(n = option(INT); {Option.value ~default:1 n}) ; id = LID ;  {id,Some (Previous n)}
    | id = LID ; SHARP ; n = INT ; {id,Some (Previous n)}
    | endrule(START | FIRST | DOLLAR) ; id = LID ;  {id,Some (At 0)}
)

%public
let tq_expr_with_pred == 
    | ~=tq_expr ; <Atom> 
    // | name = LID ; args=loption(delimited("(",separated_list(COMMA, tq_expr),")")) ; { Predicate {name;args} } 


let fol_h(atom) :=
    located(
    | FORALL_INST ; h_var = LID; AS ; binder = LID; COMMA ; f = fol_h(atom) ; {
        (* for the current instant, replace binder with original variable and remove temporal quantification for any other variable *)
        let [@warning "-4"] replace_binder = function
        | (v,t) when String.equal v binder -> (h_var,t)
        | (v,Some (Same id)) when String.equal id  binder -> (v, None)
        | x ->  x
        in 

        let past =  mk_labeled ~label:f.label (ForallPrev {h_var;binder;f})
        and curr = (map_fol_pred (map_expr Fun.id Fun.id replace_binder)) f
        
        in
        FOL_StdBinary (curr, LAnd, past)

    }
    | FORALL_PREV ; h_var = LID; AS ; binder = LID; COMMA ; f = fol_h(atom) ; {ForallPrev {h_var;binder;f}}
    | EXISTS_INST ; h_var = LID; AS ; binder = LID; COMMA ; f = fol_h(atom) ; {
        (* for the current instant, replace binder with original variable and no temporal quantification *)
         let [@warning "-4"] replace_binder = function
        | (v,t) when String.equal v binder -> (h_var,t)
        | (v,Some (Same id)) when String.equal id  binder -> (v, None)
        | x ->  x
        in 

        let past =  mk_labeled ~label:f.label (ExistsPrev {h_var;binder;f})
        and curr = (map_fol_pred (map_expr Fun.id Fun.id replace_binder)) f
        
        in
        FOL_StdBinary (curr, LOr, past)
    }
    | EXISTS_PREV ; h_var = LID; AS ; binder = LID; COMMA ; f = fol_h(atom) ; {ExistsPrev {h_var;binder;f}}
    )
    | fol(atom)


%public
let inst_spec == braced(fol(spec_expr_with_pred))
%public
let temporal_spec == ltl(braced(fol_h(tq_expr_with_pred)))
