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
    prog_setup = midrule(
            SETUP ; ":" ; setup_ensures= setup_ensures* ; setup_body=stmt* ; 
            {{setup_ensures;setup_body}}
    )? ;
    LOOP ; ":" ; main_loop_inv = invariant? ; main_body = stmt* ; EOF ;
    {
        {
            prog_decls;
            prog_spec={requires;ensures};
            prog_setup; 
            prog_main = {main_loop_inv ; main_body}
        }
    }

let invariant == preceded(INVARIANT, braced(fol)) 

let variant == ~ = preceded(VARIANT, braced(expr)); <mk_variant>

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
let typed_state_id := ids = ID+ ; COLON ; t = ty ;  {List.map (fun id -> id,(State,t)) ids}

let ty :=
    | TY_BOOL ; { Ty_Bool }
    | TY_INT ; { Ty_Int }

let stmt := located (
    | ~ = ID ; ":=" ; ~ = expr ; ";" ; <Assign>
    | EMIT ; ~ = expr  ; TO ; ~ = ID ; ";" ; <Emit>
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
        | PREV ; ~ = ID ; <Prev> 
        | e1 = expr ; op = binExpOp ; e2 = expr ; {BinOp (e1,op,e2)}
        )
    | ~ = delimited("(",expr,")") ; <>


%public
let fol := 
    | located(
        | TRUE ; {FOL_True}
        | FALSE ; {FOL_False}
        | ~ = expr ; <Pred>
        | ~ = common_logic_unary ; ~ = fol ; <FOL_Unary>
        | f1 = fol ; op = common_logic_binary ; f2 = fol ; {FOL_Binary (f1,op,f2)}
        | FORALL ; vars = typed_state_id+ ; COMMA ; f = fol ; {Forall (List.flatten vars, f)}
        | EXISTS ; vars = typed_state_id+ ; COMMA ; f = fol ; {Exists (List.flatten vars , f)}
    )
    | ~ = delimited("|",fol,"|") ; <> 

%public 
let common_logic_unary == 
    | NOT ; {Not}

%public
let common_logic_binary == 
    | DARROW ; {Equiv}
    | ARROW ; {Arrow}
    | OR ; {Or}
    | AND ; {And}
    | ~ = binExpOp ; <Arithm>

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
    | "<>" ; {Neq}

%public
let located(x) == ~ = x ; { mk_locatable (Some $loc) x }
