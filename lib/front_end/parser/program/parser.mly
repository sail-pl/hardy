%{
    open HardyMisc.Utils
    open SharedSyntax
    open ProgramSyntax

    (* https://github.com/ocaml/dune/issues/2450 *)
    module FrontParser = struct end
%}


%start <Program.base_program> program

%%

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
| SEP ; ~ = midrule(~ = some(basic_expr); <> | UNDERSCORE ; {None}) ; ~ = stmt_block ; ~ = preceded(ARROW,STATE)?  ; <>

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
    | CLEAR; ~ = basic_expr ; ";" ; <Clear> 
    | EMIT ; id = ID ; ";" ; {Emit ({label=None;value=Prod []}, id) }
    | EMIT ; ~ = basic_expr  ; TO ; ~ = ID ; ";" ; <Emit>
    | WHEN ; ~ = ID ; DO ; ~ = stmt* ; ~ = midrule(ELSE ; stmt*)? ; DONE ; <When>
    | IF ; ~ = basic_expr ; THEN ; ~ = stmt* ; ~ = midrule(ELSE ; stmt*)? ; END ; <If>
    | WHILE ; ~ = basic_expr ; DO ; ~ = invariant ; ~ = variant ; ~ = stmt* ; DONE ; <While>
    | e1 = basic_expr ; ":=" ; e2 = basic_expr ; ";" ; {Assign (e1,e2)}
)

let stmt_block == body = braced(stmt*)?; { Option.fold ~none:[] ~some:Fun.id body }

let invariant == preceded(INVARIANT, inst_spec) 

let variant == preceded(VARIANT, braced(basic_expr))

%public
let expr(var_e) := 
    | located (
        | LTRUE ; {True}
        | LFALSE ; {False}
        | ~ = INT ; <Int>
        | "[" ; "|" ; ~ = separated_list(";", expr(var_e)) ; "|" ; "]" ; <Array>
        | array = expr(var_e) ; "[" ; idx = expr(var_e) ; "]" ; { ArrayCell {array;idx} }
        | (id,x) = var_e ; {Var (id,x)}
        | ~ = STRING ; <String>
        | common_logic_unary ;  ~ = expr(var_e) ; <Not>
        | left = expr(var_e) ; op = binExpOp ; right = expr(var_e) ; {BinOp {left;op;right}}
        )
    | ~ = delimited("(",expr(var_e),")") ; <>
    | located (~ = delimited("(",separated_list(",", expr(var_e)),")") ; <Prod>)



let basic_expr == expr(id = ID ; {id,()})


%public 
let common_logic_unary == EMARK ; {(Not:common_logic_unary)}

%public
let common_logic_binary == 
    | DARROW ; {Equiv}
    | ARROW ; {Arrow}
    | ~ = binExpOp ; <Arithm>

let binExpOp ==
    | OR ; {Or}
    | AND ; {And}
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
let fol := 
    | located(
        | TRUE ; {FOL_True}
        | FALSE ; {FOL_False}
        | ~ = tq_expr ; <Pred>
        | ~ = common_logic_unary ; ~ = fol ; <FOL_Unary>
        | f1 = fol ; op = common_logic_binary ; f2 = fol ; {FOL_Binary (f1,op,f2)}
        | FORALL ; vars = typed_state_id+ ; COMMA ; f = fol ; {Forall (List.flatten vars, f)}
        | EXISTS_PREV ; v = ID; COMMA ; f = fol ; {ExistsPrev (v, f)}
        | EXISTS ; vars = typed_state_id+ ; COMMA ; f = fol ; {Exists (List.flatten vars , f)}
    )
    | ~ = delimited("(",fol,")") ; <> 


let typed_state_id := ids = ID+ ; COLON ; t = ty ;  {List.map (fun id -> id,(State,t)) ids}


%public
let located(x) == ~ = x ; { mk_labeled (Some $loc) x }

%public 
let some(x) == ~ = x ; <Some>