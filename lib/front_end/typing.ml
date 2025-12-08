open FrontParser.Program
open HardyMisc.Utils
open Syntax.Shared
open Syntax.Program
open Syntax.Ltl
open Syntax.Fol

(* todo: move some backend analysis here *)
let type_pgrm (p : parsed_program) : base_program = 
    (* todo: check empty intersection of inputs/outputs/variables *)
    let bindings = 
        (List.to_seq p.prog_decls.env_input |> Seq.map (fun (s,t) -> (s,(Input, t)))) |> Seq.append
        (List.to_seq p.prog_decls.env_output |> Seq.map (fun (s,t) -> (s,(Output, t)))) |> Seq.append
        (List.to_seq p.prog_decls.env_variables |> Seq.map (fun (s,t) -> (s,(State, t)))) |> Bindings.of_seq 
    in
    let type_fol_expr = map_fol_pred @@ map_expr (Fun.id) (fun (id,t) -> id,(t,Bindings.find id bindings))
    in
    let type_prog_expr = map_fol_pred @@ map_expr (Fun.id) (fun (id,()) -> id,(None,Bindings.find id bindings)) in

    let prog_spec = 

        let requires = List.map (map_ltl_pred type_fol_expr) p.prog_spec.requires 
        and ensures =  List.map (map_ltl_pred type_fol_expr) p.prog_spec.ensures in
        {requires;ensures}

    and prog_setup = Option.map (fun s -> 
        let setup_ensures = List.map type_prog_expr s.setup_ensures
        and setup_body = List.map (map_stmt Fun.id (fun (id,()) -> id,(Bindings.find id bindings)) type_prog_expr) s.setup_body in
        {setup_ensures; setup_body}

    )
    p.prog_setup 
    and prog_main = 
        let main_body = 
            List.map (map_stmt Fun.id (fun (id,()) -> id,(Bindings.find id bindings)) type_prog_expr) p.prog_main.main_body
        and main_loop_inv = Option.map type_prog_expr p.prog_main.main_loop_inv in
        {main_body; main_loop_inv}
    in
    {prog_setup; prog_main; prog_spec; prog_decls={env_variables=bindings}}

