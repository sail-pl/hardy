%{
    open HardySyntax.Locations
    open HardySyntax.Types
    open HardySyntax.Operators
    open HardySyntax.Fol
    open HardySyntax.Ltl
    open HardySyntax.Syntax
%}


%start <program> program

%%

let program :=
    prog_env = declaration ; requires = requires* ; ensures = prog_ensures*  ; 
        prog_setup = midrule(SETUP ; ":" ; setup_ensures= setup_ensures* ; setup_body=stmt* ; {{setup_ensures;setup_body} })? ;
        LOOP ; ":" ; main_invariant = invariant? ; main_body = stmt* ; EOF ;
        {
            {
                prog_env;
                prog_spec={requires;ensures};
                prog_setup; 
                prog_main = {main_invariant ; main_body}
            }
        }

let invariant := preceded(INVARIANT, braced(fol))

let variant := v = preceded(VARIANT, braced(expr)); {{var_expr=v}}

%public
let braced(x) == delimited("{", x, "}")

let declaration := 
    env_input=loption(input) ; 
    env_output=loption(output) ; 
    env_variables = loption(var) ; {{env_input;env_output;env_variables}}


let vdecl(KIND) == v = delimited(KIND, typed_id*, ";"); {List.flatten v}

let var == vdecl(VAR)

let input == vdecl(INPUT)

let output == vdecl(OUTPUT)

let typed_id := ids = ID+ ; COLON ; t = ty ; {List.map (fun id -> id,t) ids}

let ty :=
    | TY_BOOL ; { Ty_Bool }
    | TY_INT ; { Ty_Int }

let stmt := located (
    | ~ = ID ; ":=" ; ~ = expr ; ";" ; <Assign>
    | EMIT ; ~ = ID ; ~ = expr ; ";" ; <Emit>
    | IF ; ~ = expr ; THEN ; ~ = stmt* ; ~ = midrule(ELSE ; stmt*)? ; END ; <If>
    | WHILE ; ~ = expr ; DO ; ~ = invariant ; ~ = variant ; ~ = stmt* ; DONE ; <While>
)

let expr := 
    | located (
        | LTRUE ; {True}
        | LFALSE ; {False}
        | ~ = INT ; <Int>
        | ~ = ID  ; <Var>
        | READ ; ~ = ID ; <Read>
        // | OLD ; ~ = ID ; <Old> 
        | e1 = expr ; op = binExpOp ; e2 = expr ; {BinOp (e1,op,e2)}
        )
    | LPAREN ; ~ = expr ; RPAREN ; <>


%public
let fol := 
    | located(
        | TRUE ; {FOL_True}
        | FALSE ; {FOL_False}
        | ~ = expr ; <Pred>
        | ~ = common_logic_unary ; ~ = fol ; <FOL_Unary>
        | f1 = fol ; op = common_logic_binary ; f2 = fol ; {FOL_Binary (f1,op,f2)}
        | FORALL ; vars = typed_id+ ; COMMA ; f = fol ; {Forall (List.flatten vars, f)}
        | EXISTS ; vars = typed_id+ ; COMMA ; f = fol ; {Exists (List.flatten vars , f)}
    )
    | ~ = delimited(LSQBRACE,fol,RSQBRACE) ; <> // can't use () because fol includes expr 


%public 
let common_logic_unary == 
    | NOT ; {Not}

%public
let common_logic_binary == 
    | XOR ; {Xor}
    | DARROW ; {Equiv}
    | ARROW ; {Arrow}
    | OR ; {Or}
    | AND ; {And}
    // | ~ = binExpOp ; <Arithm>

let binExpOp ==
    | "+" ; {Add} 
    | "-" ; {Sub}
    | "*" ; {Mul}
    | "/" ; {Div}
    | "<" ; {Lt}
    | "<=" ; {Lte}
    | ">" ; {Gt}
    | ">=" ; {Gte}
    | "=" ; {Eq}

%public
let located(x) == ~ = x ; { mk_locatable (Some $loc) x }
