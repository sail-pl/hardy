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

let setup_ensures == ENSURES ;  ~ = braced(inst_spec) ;  <>

let invariant == preceded(INVARIANT, braced(inst_spec)) 

let variant == ~ = preceded(VARIANT, braced(basic_expr)); <mk_variant>

// end specification ---------

let program :=
    prog_decls = declaration ; 
    requires = prog_requires* ; 
    ensures = prog_ensures* ; 
    prog_setup = midrule(
            SETUP ; ":" ; setup_ensures= setup_ensures* ; setup_body=stmt* ; 
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
    env_variables = loption(var) ; {{env_input;env_output;env_variables}}


let vdecl(KIND) == v = delimited(KIND, typed_decl_id*, ";"); {List.flatten v}

let var == vdecl(VAR)

let input == vdecl(INPUT)

let output == vdecl(OUTPUT)

let typed_decl_id := ids = ID+ ; COLON ; t = ty ;  {List.map (fun id -> id,t) ids}

let typed_decl_id_opt := ids = ID+ ; t = preceded(COLON , ty)?;  {List.map (fun id -> id,t) ids}


let ty :=
    | TY_BOOL ; {Ty_Bool}
    | TY_INT ; {Ty_Int}
    | TY_REAL ; {Ty_Real}
    | TY_STRING ; {Ty_String}
    | t = ty ; TY_ARRAY ;  {Ty_Array (t,None)}

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
    | r = REAL ; { let (~radix,~num,~frac,~exp) = r in Real {radix; num; frac; exp}}
    | "[" ; "|" ; l = separated_nonempty_list(";", expr(var_e)) ; "|" ; "]" ; {Array (Iarray.of_list l)} (* array litterals cannot be empty *)
    | ~ = simpl_expr(var_e) ; "[" ; ~ = expr(var_e) ; "]" ; <ArrayCell>
    | ~ = STRING ; <String>
    | (id,x) = var_e ; {Var (id,x)}
)

(*         | name = ID ; args=loption(delimited("(",separated_list(COMMA, atom),")"))  {FOL_Atom (Predicate {name;args=[]}) } *)

let expr(var_e) := 
    | located (
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
        | ~=delimited(LBRACE,atom,RBRACE) ; <FOL_Atom>
        | ~ = common_logic_unary ; ~ = fol(atom) ; %prec UNARY <FOL_StdUnary>
        | f1 = fol(atom) ; op = common_logic_binary ; f2 = fol(atom) ; {FOL_StdBinary (f1,op,f2)}
        | FORALL_PREV ; h_var = ID; AS ; binder = ID; COMMA ; f = fol(atom) ; {ForallPrev {h_var;binder;f}}
        | EXISTS_PREV ; h_var = ID; AS ; binder = ID; COMMA ; f = fol(atom) ; {ExistsPrev {h_var;binder;f}}
        | FORALL ; vars = typed_decl_id_opt+ ; COMMA ; f = fol(atom) ; {Forall (List.flatten vars, f)}
        | EXISTS ; vars = typed_decl_id_opt+ ; COMMA ; f = fol(atom) ; {Exists (List.flatten vars , f)}
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
