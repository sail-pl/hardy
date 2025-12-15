%{
    open HardyMisc.Utils
    open SharedSyntax
    open ProgramSyntax

    (* https://github.com/ocaml/dune/issues/2450 *)
    module FrontParser = struct end
%}


%start <Program.parsed_program> program

%%

// begin specification ------

let inst_spec == fol(expr_with_pred)
let ltl_spec == ltl(braced(fol(tq_expr_with_pred)))


let prog_requires == RELY ; ~ =  ltl_spec ;  <>

let prog_ensures == GUARANTEE ; ~ =  ltl_spec ;<>

let function_requires == REQUIRES ;  ~ = braced(inst_spec) ;  <>
let function_ensures == ENSURES ;  ~ = braced(inst_spec) ;  <>

let invariant == preceded(INVARIANT, braced(inst_spec)) 

let variant == ~ = preceded(VARIANT, braced(basic_expr)); <mk_variant>

// end specification ---------

let program :=
    prog_decls = declaration ; 
    requires = prog_requires* ; 
    ensures = prog_ensures* ; 
    prog_setup = midrule(
            SETUP ; ":" ; setup_ensures= function_ensures* ; setup_body=stmt* ; 
            {{setup_ensures;setup_body}}
    )? ;
    LOOP ; ":" ; main_loop_inv = invariant* ; main_body = stmt* ; EOF ;
    {
        {
            prog_decls;
            prog_spec={requires;ensures;data=()};
            prog_setup; 
            prog_main = {main_loop_inv ; main_body}
        }
    }

%public
let braced(x) == delimited("{", x, "}")

let declaration := 
    env_input=loption(input) ; 
    env_output=loption(output) ; 
    env_variables = loption(var) ; 
    env_functions = func* ;
    // env_spec_predicates = loption(predicate) ;
    {{env_input;env_output;env_variables; env_functions}}


let vdecl(KIND) == v = delimited(KIND, typed_decl_id*, ";"); {List.flatten v}

let var == vdecl(VAR)

let input == vdecl(INPUT)

let output == vdecl(OUTPUT)

// let predicate := 
//     | PREDICATE ; ID ; args = delimited("(", separated_list(COMMA, ID) ,")")? ; "=" ; body =  
    
//      {}


let func :=
    | FUNCTION ; 
        f_name = ID ; f_args = delimited("(", separated_list(COMMA, ID) ,")") ; 
        f_requires = function_requires* ;
        f_ensures = function_ensures* ;
        f_body = preceded ("=", stmt*) ; 
        { {f_name; f_args; f_requires ; f_ensures ; f_body} }


let typed_decl_id := ids = ID+ ; COLON ; t = ty ;  {List.map (fun id -> id,t) ids}

let ty :=
    | TY_BOOL ; { Ty_Bool }
    | TY_INT ; { Ty_Int }

let stmt := located (
    | e1 = basic_expr ; ":=" ; e2 = basic_expr ; ";" ; {Assign (e1,e2)}
    | EMIT ; ~ = basic_expr  ; TO ; ~ = ID ; ";" ; <Emit>
    | IF ; ~ = basic_expr ; THEN ; ~ = stmt* ; ~ = midrule(ELSE ; stmt*)? ; END ; <If>
    | WHILE ; ~ = basic_expr ; DO ; ~ = invariant ; ~ = variant ; ~ = stmt* ; DONE ; <While>
)


let simpl_expr(var_e) :=
| located (
    | LTRUE ; {True}
    | LFALSE ; {False}
    | ~ = INT ; <Int>
    | (id,x) = var_e ; {Var (id,x)}
)


let expr(var_e) := 
    | located (
        | ~ = ID ; ~=delimited("(", separated_list(COMMA, expr(var_e)) ,")") ; <Function>
        | EMARK ;  e = expr(var_e) ; %prec UNARY {UnOp (ENot,e)}
        | left = expr(var_e) ; op = binExpOp ; right = expr(var_e) ; {BinOp {left;op;right}}
        )
    | ~ = delimited("(",expr(var_e),")") ; <>
    | simpl_expr(var_e)


let basic_expr == expr(id = ID ; {id,()})

let expr_with_pred := ~= basic_expr ; <Atom>


let tq_expr == expr(
    | id = ID ; {id,None}
    | id = ID ; endrule(AT|SYMB_AT) ; n = INT ; {id,Some (At n)}
    | endrule(PREV | LAST) ; n = endrule(n = option(INT); {Option.value ~default:1 n}) ; id = ID ;  {id,Some (Previous n)}
    | id = ID ; SHARP ; n = INT ; {id,Some (Previous n)}
    | endrule(START | FIRST | DOLLAR) ; id = ID ;  {id,Some (At 0)}
)

let tq_expr_with_pred := 
    | ~=tq_expr ; <Atom>
    // | name = ID ; args=loption(delimited("(",separated_list(COMMA, tq_expr),")")) ; { Predicate {name;args} }



%public
let fol(atom) := 
    | located(
        | TRUE ; {FOL_True}
        | FALSE ; {FOL_False} 
        | ~=atom ; <FOL_Atom>
        | ~ = common_logic_unary ; ~ = fol(atom) ; %prec UNARY <FOL_StdUnary>
        | f1 = fol(atom) ; op = common_logic_binary ; f2 = fol(atom) ; {FOL_StdBinary (f1,op,f2)}
        | FORALL ; vars = typed_decl_id+ ; COMMA ; f = fol(atom) ; {Forall (List.flatten vars, f)}
        | EXISTS_PREV ; v = ID; COMMA ; f = fol(atom) ; {ExistsPrev (v, f)}
        | EXISTS ; vars = typed_decl_id+ ; COMMA ; f = fol(atom) ; {Exists (List.flatten vars , f)}
    )
    | ~ = delimited("(",fol(atom),")") ; <> 

%public 
let common_logic_unary == EMARK ; {LNot}

%public
let common_logic_binary == 
    | DARROW ; {Equiv}
    | ARROW ; {Arrow}
    | OR ; {LOr}
    | AND ; {LAnd}


let binExpOp ==
    | OR ; {EOr}
    | AND ; {EAnd}
    | "+" ; {Add} 
    | "-" ; {Sub}
    | "*" ; {Mul}
    | "/" ; {Div}
    | "<" ; {Lt}
    | "<=" ; {Lte}
    | ">" ; {Gt}
    | ">=" ; {Gte}
    | "=" ; {Eq}
    | "<>" ; {Neq}


%public
let located(x) == ~ = x ; { mk_labeled (Some $loc) x }
