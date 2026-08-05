%{
    open HardyMisc.Utils
    open SharedSyntax
%}



%%


%public
let braced(x) == delimited("{", x, "}")

%public
let sqbracketed(x) == delimited("[", x, "]")

%public
let simple_ty :=
    | TY_UNIT ; {Ty_Prod []}
    | TY_BOOL ; {Ty_Bool}
    | TY_INT ; {Ty_Int}
    | TY_REAL ; {Ty_Real}
    | TY_STRING ; {Ty_String}

%public
let ty := 
    | ~ = simple_ty ; <>
    | l = ty ; "*"; r = simple_ty; {Ty_Prod [l;r]}
    | ~ = delimited("(", ty, ")") ; <>
    | t = ty ; TY_ARRAY ;  {Ty_Array (t,None)}


%public
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
    | simpl_expr(id = LID ; {id,()})
    | ~=delimited("(", pgrm_expr, ")") ; <>
    | located (
        | array = simpl_expr(id = LID ; {id,()}) ; "[" ; idx = pgrm_expr ; "]" ; {ArrayCell {idx;array}}
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
let spec_expr_with_pred == ~= spec_expr(id = LID ; {id,()}) ; <Atom>

%public
let typed_decl_id_opt := ~=pair(LID,preceded(COLON , ty)?);  <>

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

%public
let pgrmBinExpOp ==
    | "+" ; {Add} 
    | "-" ; {Sub}
    | "*" ; {Mul}
    | "/" ; {Div}

%public
let comparator == 
    | "=" ; {Eq}
    | "<" ; {Lt}
    | "<=" ; {Lte}
    | ">" ; {Gt}
    | ">=" ; {Gte}
    | "<>" ; {Neq}

%public
let pgrmBinExpOpFull ==
    | ~ = comparator; <> 
    | OR ; {EOr}
    | AND ; {EAnd}
    | ~ = pgrmBinExpOp; <>

%public
let located(x) == ~ = x ; { mk_labeled ~label:(Some $loc) x }
