%{
    open HardyMisc.Utils
    open SharedSyntax
    open Loopy.Syntax
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
    pre = prog_requires* ; 
    post = prog_ensures* ; 
    prog_setup = midrule(
            SETUP ; ":" ; setup_ensures= setup_ensures* ; setup_body= loption(seq_stmt) ; 
            {{setup_ensures;setup_body}}
    )? ;
    LOOP ; ":" ; main_loop_inv = invariant* ; main_body = loption(seq_stmt) ; EOF ;
    {
        
        {
            prog = {
                prog_decls;
                prog_setup; 
                prog_main = {main_loop_inv ; main_body}
            } ;
            
            prog_spec=mk_labeled ~label:() {pre;post};
        }
    }


let declaration := 
    env_input=loption(input) ; 
    env_output=loption(output) ; 
    env_variables = loption(var) ; {{env_input;env_output;env_variables}}


let vdecl(KIND) == v = delimited(KIND, typed_decl_id*, ";"); {List.flatten v}

let var == vdecl(VAR)

let input == vdecl(INPUT)

let output == vdecl(OUTPUT)

let typed_decl_id := ids = LID+ ; COLON ; t = ty ;  {List.map (fun id -> id,t) ids}

let stmt := located (
    | e1 = pgrm_expr ; ":=" ; e2 = pgrm_expr ; {Assign (e1,e2)}
    | EMIT ; id = LID  ; {Emit ({label=None;value=Prod []}, id) }
    | EMIT ; ~ = pgrm_expr  ; TO ; ~ = LID ; <Emit>
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
