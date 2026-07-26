%{
    open HardyMisc.Utils
    open SharedSyntax
    open ProgramSyntax
    (* open InstantSyntax *)

    (* https://github.com/ocaml/dune/issues/2450 *)
    module FrontParser = struct end
%}



%%

// begin specification ------

let prog_requires == ASSUMES ; ~ =  temporal_spec ;  <>

let prog_ensures == GUARANTEES ; ~ =  temporal_spec ;<>

let setup_ensures == ENSURES ;  ~ = inst_spec ;  <>

let invariant == preceded(INVARIANT, inst_spec) 

let variant == ~ = preceded(VARIANT, braced(pgrm_expr)); <mk_variant>

// end specification ---------

let program :=
    prog_decls = declaration ; 
    requires = prog_requires* ; 
    ensures = prog_ensures* ; 
    prog_setup = midrule(
            SETUP ; ":" ; setup_ensures= setup_ensures* ; setup_body= loption(seq_stmt) ; 
            {{setup_ensures;setup_body}}
    )? ;
    LOOP ; ":" ; main_loop_inv = invariant* ; main_body = loption(seq_stmt) ; EOF ;
    {
        {
            prog_decls;
            prog_spec=mk_labeled ~label:() {requires;ensures};
            prog_setup; 
            prog_main = {main_loop_inv ; main_body}
        }
    }

%public
let braced(x) == delimited("{", x, "}")

%public
let sqbracketed(x) == delimited("[", x, "]")

let declaration := 
    env_input=loption(input) ; 
    env_output=loption(output) ; 
    env_variables = loption(var) ; {{env_input;env_output;env_variables}}


let vdecl(KIND) == v = delimited(KIND, typed_decl_id*, ";"); {List.flatten v}

let var == vdecl(VAR)

let input == vdecl(INPUT)

let output == vdecl(OUTPUT)

let typed_decl_id := ids = ID+ ; COLON ; t = ty ;  {List.map (fun id -> id,t) ids}

let typed_decl_id_opt := ~=pair(ID,preceded(COLON , ty)?);  <>


let simple_ty :=
    | TY_UNIT ; {Ty_Prod []}
    | TY_BOOL ; {Ty_Bool}
    | TY_INT ; {Ty_Int}
    | TY_REAL ; {Ty_Real}
    | TY_STRING ; {Ty_String}

let ty := 
    | ~ = simple_ty ; <>
    | l = ty ; "*"; r = simple_ty; {Ty_Prod [l;r]}
    | ~ = delimited("(", ty, ")") ; <>
    | t = ty ; TY_ARRAY ;  {Ty_Array (t,None)}

let stmt := located (
    | e1 = pgrm_expr ; ":=" ; e2 = pgrm_expr ; {Assign (e1,e2)}
    | EMIT ; id = ID  ; {Emit ({label=None;value=Prod []}, id) }
    | EMIT ; ~ = pgrm_expr  ; TO ; ~ = ID ; <Emit>
)

let controle_stmt := located(
    | IF ; ~ = pgrm_expr ; THEN ; ~ = seq_stmt ; ~ = midrule(ELSE ; seq_stmt)? ; END ; <If>
    | WHILE ; ~ = pgrm_expr ; DO ; ~ = invariant ; ~ = variant ; ~ = seq_stmt ; DONE ; <While>
)

let seq_stmt := 
    | x = endrule(controle_stmt | stmt) ; ";"? ; {[x]}
    | hd = controle_stmt ; ";"? ; tl = seq_stmt ; {hd::tl}
    | hd = stmt ; ";" ; tl = seq_stmt ; {hd::tl}

// let stmt_block := loption(braced(seq_stmt))

let simpl_expr(var_e) :=
| located (
    | LTRUE ; {True}
    | LFALSE ; {False}
    | ~ = INT ; <Int>
    | r = REAL ; { let (~radix,~num,~frac,~exp) = r in Real {radix; num; frac; exp}}
    | ~ = STRING ; <String>
    | "(" ; ")" ; { Prod [] }
    | (id,x) = var_e ; {Var (id,x)}
)

%public
let pgrm_expr := 
    | simpl_expr(id = ID ; {id,()})
    | ~=delimited("(", pgrm_expr, ")") ; <>
    | located (
        | array = simpl_expr(id = ID ; {id,()}) ; "[" ; idx = pgrm_expr ; "]" ; {ArrayCell {idx;array}}
        | EMARK ;  e = pgrm_expr ; %prec UNARY {UnOp (ENot,e)}
        | "[" ; "|" ; l = separated_nonempty_list(";", pgrm_expr) ; "|" ; "]" ; {Array (Iarray.of_list l)} (* array litterals cannot be empty *)
        | left = pgrm_expr ; op = pgrmBinExpOpFull ; right = pgrm_expr ; {BinOp {left;op;right}}
        | ~=tuple(pgrm_expr) ; %prec below_COMMA <Prod>
    )

%public
// same as pgrm_expr except operators shared with the fol layer are removed
let spec_expr(var_e) := 
    | simpl_expr(var_e)
    | located (
        | array = simpl_expr(var_e) ; "[" ; idx = spec_expr(var_e) ; "]" ; {ArrayCell {idx;array}}
        | "[" ; "|" ; l = separated_nonempty_list(";", spec_expr(var_e)) ; "|" ; "]" ; {Array (Iarray.of_list l)} (* array litterals cannot be empty *)
        | left = spec_expr(var_e) ; op = pgrmBinExpOp ; right = spec_expr(var_e) ; {BinOp {left;op;right}}
        | ~=tuple(spec_expr(var_e)) ; %prec below_COMMA <Prod>
    )

let reversed_tuple_body(e) :=
    | t = reversed_tuple_body(e) ; "," ; e = e ; { e::t }
    | e1 = e ; "," ; e2 =e ; { [e2;e1] }

let tuple(e) == rev(reversed_tuple_body(e))



%public
let spec_expr_with_pred == ~= spec_expr(id = ID ; {id,()}) ; <Atom>


%public
let fol(atom) := 
    | located(
        | TRUE ; {FOL_True}
        | FALSE ; {FOL_False} 
        | ~=atom; <FOL_Atom>
        | ~ = common_logic_unary ; ~ = fol(atom) ; %prec UNARY <FOL_StdUnary>
        | ~ = fol(atom) ; ~ = endrule(c = comparator; {Program (string_of_pgrm_op c)}) ; ~ = fol(atom) ; <FOL_StdBinary>
        | ~ = fol(atom) ; ~ = common_logic_binary ; ~ = fol(atom) ; <FOL_StdBinary>
        | FORALL ; ~ = typed_decl_id_opt+ ; COMMA ; ~ = fol(atom)  ; <Forall>
        | EXISTS ; ~ = typed_decl_id_opt+ ; COMMA ; ~ = fol(atom) ; <Exists>
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


let pgrmBinExpOp ==
    | "+" ; {Add} 
    | "-" ; {Sub}
    | "*" ; {Mul}
    | "/" ; {Div}

let comparator == 
    | "=" ; {Eq}
    | "<" ; {Lt}
    | "<=" ; {Lte}
    | ">" ; {Gt}
    | ">=" ; {Gte}
    | "<>" ; {Neq}

let pgrmBinExpOpFull ==
    | ~ = comparator; <> 
    | OR ; {EOr}
    | AND ; {EAnd}
    | ~ = pgrmBinExpOp; <>







%public
let located(x) == ~ = x ; { mk_labeled ~label:(Some $loc) x }
