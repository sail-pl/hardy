%{
    open HardyMisc.Utils
    open SharedSyntax
    open ProgramSyntax
    open InstantSyntax 

    (* https://github.com/ocaml/dune/issues/2450 *)
    module FrontParser = struct end
%}


%start <Program.parsed_program> program

%%

// begin specification ------

let inst_spec == fol(tq_expr_with_pred)
let pltl_atom == braced(inst_spec)
let ltl_atom == braced(pltl(pltl_atom))
let ltl_spec == ltl(ltl_atom)

let node_assumes == ASSUMES; ~ =  ltl_spec ; <>

let node_guarantees == GUARANTEES ; ~ =  inst_spec ;<>

let node_requires == REQUIRES ; ~ =  ltl_spec ;  <>

let node_ensures == ENSURES ;  ~ = ltl_spec ;  <>

let invariant == preceded(INVARIANT, pltl_atom) 

let variant == ~ = preceded(VARIANT, braced(basic_expr)); <mk_variant>

// end specification ---------

let program :=
    prog_nodes = node+; EOF; { {prog_nodes} }

let node := 
    node_spec = midrule(
        n_requires=node_requires* ; 
        n_ensures=node_ensures* ; 
        n_assumes=node_assumes* ;
        n_guarantees=node_guarantees*;
        {{n_requires;n_ensures;n_assumes;n_guarantees}} 
    ) ;
    NODE; node_id = delimited("<", UID, ">")  ; 
    node_params = delimited("(", flatten(separated_list(",", typed_decl_id)), ")") ;
    node_rtype = preceded(":", ty) ; 
    node_vars = loption(vdecl(VAR));
    node_preamble = stmt_block ;
    "=" ; node_body = seq_stmt;
    { {node_id; node_rtype; node_params; node_vars; node_spec; node_preamble;node_body} }

%public
let braced(x) == delimited("{", x, "}")

let vdecl(KIND) == v = delimited(KIND, typed_decl_id*, ";"); {List.flatten v}


let typed_decl_id := ids = LID+ ; COLON ; t = ty ;  {List.map (fun id -> id,t) ids}


%public
let ty :=
    | TY_UNIT ; {Ty_Prod []}
    | TY_BOOL ; {Ty_Bool}
    | TY_INT ; {Ty_Int}
    | TY_STRING ; {Ty_String}
    | l = ty ; "*"; r = ty ; {Ty_Prod [l;r]}
    | TY_ARRAY ; LT ; ~ = ty ; ";" ; ~ = INT ; GT ; <Ty_Array>

let stmt := located (
    | RETURN; ~ = basic_expr; ";" ; <Return>
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
    | "(" ; ")" ; {Unit}
    | (id,x) = var_e ; {Var (id,x)}
)

(*         | name = ID ; args=loption(delimited("(",separated_list(COMMA, atom),")"))  {FOL_Atom (Predicate {name;args=[]}) } *)

%public
let expr(var_e) := 
    | simpl_expr(var_e)
    | ~ = delimited("(",expr(var_e),")") ; <> 
    | located (
        | node_id = UID ; args=expr(var_e) ; {NodeCall {node_id;args} }
        | array = simpl_expr(var_e) ; "[" ; idx = expr(var_e) ; "]" ; {ArrayCell {idx;array}}
        // | EMARK ;  e = expr(var_e) ; %prec UNARY {UnOp (ENot,e)}
        | "[" ; "|" ; ~ = separated_nonempty_list(";", expr(var_e)) ; "|" ; "]" ; <Array>
        | left = expr(var_e) ; op = binExpOp ; right = expr(var_e) ; {BinOp {left;op;right}}
        | ~ = tuple(var_e) ; %prec below_COMMA <Prod>
        )

let reversed_tuple_body(var_e) :=
    | t = reversed_tuple_body(var_e) ; "," ; e = expr(var_e) ; { e::t }
    | e1 = expr(var_e) ; "," ; e2 = expr(var_e) ; { [e2;e1] }

let tuple(var_e) == rev(reversed_tuple_body(var_e))

let basic_expr == expr(id = LID ; {id,()})


%public
let fol(atom) := 
    | located(
        | TRUE ; {FOL_True}
        | FALSE ; {FOL_False} 
        | ~=atom ; <FOL_Atom>
        | ~ = common_logic_unary ; ~ = fol(atom) ; %prec UNARY <FOL_StdUnary>
        | f1 = fol(atom) ; op = common_logic_binary ; f2 = fol(atom) ; {FOL_StdBinary (f1,op,f2)}
        | FORALL ; vars = typed_id+ ; COMMA ; f = fol(atom) ; {Forall (List.flatten vars, f)}
        // | EXISTS_PREV ; v = LID; COMMA ; f = fol(atom) ; {ExistsPrev (v, f)}
        | EXISTS ; vars = typed_id+ ; COMMA ; f = fol(atom) ; {Exists (List.flatten vars , f)}
    )
    | ~ = delimited("(",fol(atom),")") ; <> 

let typed_id := ids = LID+ ; COLON ; t = ty ;  {List.map (fun id -> id,(State,t)) ids}

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
