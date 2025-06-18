%{
    open HardyMisc.Utils
    open SharedSyntax
    open ProgramSyntax
    open InstantSyntax

    (* https://github.com/ocaml/dune/issues/2450 *)
    module FrontParser = struct end
%}


%start <Program.base_program> program

%%

// begin specification ------

let inst_spec == fol(tq_expr)
let ltl_spec == ltl(braced(inst_spec))


let prog_requires == RELY ; ~ =  ltl_spec ;  <>

let prog_ensures == GUARANTEE ; ~ =  ltl_spec ;<>

let state_requires == REQUIRES ;  ~ = braced(inst_spec) ;  <>

let state_ensures == ENSURES ;  ~ = braced(inst_spec) ;  <>

let invariant == preceded(INVARIANT, braced(inst_spec)) 

let variant == ~ = preceded(VARIANT, braced(basic_expr)); <mk_variant>

// end specification ---------

let program :=
    prog_decls = declaration ; 
    requires = prog_requires* ; 
    ensures = prog_ensures* ; 
    prog_nodes = state+;
    EOF;
    {
        {
            prog_decls;
            prog_spec={requires;ensures};
            prog_nodes
        }
    }

let state := 
    node_id=STATE ; ":" ; 
    node_variables = loption(vdecl(LOCAL));
    node_spec = midrule(requires=state_requires* ; ensures=state_ensures* ; {{requires;ensures}} ) ;
    node_preamble = stmt_block ;
    node_transitions = transition* ;
    { {node_id; node_variables; node_spec; node_preamble; node_transitions} }



let transition := 
| SEP ; ~ = midrule(~ = basic_expr; <Some> | UNDERSCORE ; {None}) ; ~ = stmt_block ; ~ = preceded(ARROW,STATE)?  ; <>

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

%public
let ty :=
    | TY_UNIT ; {Ty_Prod []}
    | TY_BOOL ; {Ty_Bool}
    | TY_INT ; {Ty_Int}
    | TY_STRING ; {Ty_String}
    | l = ty ; "*"; r = ty ; {Ty_Prod [l;r]}
    | TY_ARRAY ; LT ; ~ = ty ; ";" ; ~ = INT ; GT ; <Ty_Array>

let stmt := located (
    | CLEAR; ~ = basic_expr ; <Clear> 
    | EMIT ; id = ID  ; {Emit ({label=None;value=Prod []}, id) }
    | EMIT ; ~ = basic_expr  ; TO ; ~ = ID ; <Emit>
    | WHEN ; ~ = ID ; DO ; ~ = seq_stmt ; ~ = midrule(ELSE ; seq_stmt)? ; DONE ; <When>
    | IF ; ~ = basic_expr ; THEN ; ~ = seq_stmt ; ~ = midrule(ELSE ; seq_stmt)? ; END ; <If>
    | WHILE ; ~ = basic_expr ; DO ; ~ = invariant ; ~ = variant ; ~ = seq_stmt ; DONE ; <While>
    | e1 = basic_expr ; ":=" ; e2 = basic_expr ; {Assign (e1,e2)}
)

let seq_stmt := 
    | x = stmt ; {[x]}
    | x = stmt ; ";" ; {[x]}
    | hd = stmt ; ";" ; tl = seq_stmt ; {hd::tl}

let stmt_block := loption(braced(seq_stmt))

let simpl_expr(var_e) :=
| located (
    | LTRUE ; {True}
    | LFALSE ; {False}
    | ~ = INT ; <Int>
    | ~ = STRING ; <String>
    | (id,x) = var_e ; {Var (id,x)}
)

let expr(var_e) := 
    | ~ = delimited("(", expr(var_e), ")") ; <>
    | simpl_expr(var_e)
    | located (
        | array = simpl_expr(var_e) ; "[" ; idx = expr(var_e) ; "]" ; {ArrayCell {idx;array}}
        | EMARK ;  e = expr(var_e) ; %prec UNARY {UnOp (ENot,e)}
        | "[" ; "|" ; ~ = separated_nonempty_list(";", expr(var_e)) ; "|" ; "]" ; <Array>
        | left = expr(var_e) ; op = binExpOp ; right = expr(var_e) ; {BinOp {left;op;right}}
        | ~ = tuple(var_e) ; %prec below_COMMA <Prod>
        )

let reversed_tuple_body(var_e) :=
    | t = reversed_tuple_body(var_e) ; "," ; e = expr(var_e) ; { e::t }
    | e1 = expr(var_e) ; "," ; e2 = expr(var_e) ; { [e2;e1] }

let tuple(var_e) == rev(reversed_tuple_body(var_e))

let basic_expr == expr(id = ID ; {id,()})


let tq_expr := expr(
    | id = ID ; {id,None}
    | id = ID ; endrule(AT|SYMB_AT) ; n = INT ; {id,Some (At n)}
    | endrule(PREV | LAST) ; n = endrule(n = option(INT); {Option.value ~default:1 n}) ; id = ID ;  {id,Some (Previous n)}
    | id = ID ; SHARP ; n = INT ; {id,Some (Previous n)}
    | endrule(START | FIRST | DOLLAR) ; id = ID ;  {id,Some (At 0)}
)


%public
let fol(atom) := 
    | located(
        | TRUE ; {FOL_True}
        | FALSE ; {FOL_False}
        | ~ = atom ; <FOL_Atom>
        | ~ = common_logic_unary ; ~ = fol(atom) ; %prec UNARY <FOL_StdUnary>
        | f1 = fol(atom) ; op = common_logic_binary ; f2 = fol(atom) ; {FOL_StdBinary (f1,op,f2)}
        | FORALL ; vars = typed_state_id+ ; COMMA ; f = fol(atom) ; {Forall (List.flatten vars, f)}
        | EXISTS_PREV ; v = ID; COMMA ; f = fol(atom) ; {ExistsPrev (v, f)}
        | EXISTS ; vars = typed_state_id+ ; COMMA ; f = fol(atom) ; {Exists (List.flatten vars , f)}
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


let typed_state_id := ids = ID+ ; COLON ; t = ty ;  {List.map (fun id -> id,(State,t)) ids}


%public
let located(x) == ~ = x ; { mk_labeled (Some $loc) x }