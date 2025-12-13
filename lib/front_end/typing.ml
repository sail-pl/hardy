open FrontParser.Program
open HardyMisc.Utils
open Syntax.Shared
open Syntax.Program
open Syntax.Ltl
open Syntax.Fol

let reserved_words = ["result" ; "old" ;  "list" ; "int"] (* todo: add more*)

let fail_if_reserved s = if List.mem s reserved_words then Format.sprintf "'%s' is a reserved word" s |> failwith else s

let type_pgrm (p : parsed_program) : frontend_program = 
    let bindings = 
        let open Bindings in
        let check_dup = fun x (cat1,_) (cat2,_) -> 
            Format.asprintf "duplicate %a and %a variable %s" Printer.pp_cat_ty cat1 Printer.pp_cat_ty cat2 x |> failwith
        in

        let inputs = List.map (fun (s,t) -> (fail_if_reserved s,(Input, t))) p.prog_decls.env_input |> of_list
        and outputs = List.map (fun (s,t) -> (fail_if_reserved s,(Output, t))) p.prog_decls.env_output |> of_list
        and states = List.map (fun (s,t) -> (fail_if_reserved s,(State, t))) p.prog_decls.env_variables |> of_list in
        
        union check_dup inputs outputs |> fun io -> union check_dup io states
    in

    let requires_checks = fun acc e -> match e.value with 
        | Var (_,(None,(Output,_))) -> 
            failwith "output variables within 'relies on' spec cannot mention current output, only past"
        | Var (_,(_,(Input,_))) ->
            {acc with mentions_input = true;}
        | Var (_,(_,(Output,_))) ->
            {acc with mentions_output = true;}                       
        | Var (_,(_,(State,_))) ->
            failwith "'relies on' spec cannot mention state variables"
        | _ -> acc
        
    and ensures_checks = (fun acc e -> match e.value with 
                | Var (_,(_,(Input,_))) ->
                    {acc with mentions_input = true;}
                | Var (_,(_,(Output,_))) ->
                    {acc with mentions_output = true;}                       
                | Var (_,(_,(State,_))) ->
                    {acc with mentions_state = true;}      
                | _ -> acc
        )     
    and fold_fol_prop c = fold_fol (fun acc _ -> acc) (fun acc -> function
        | Atom e -> fold_expr c acc e
        | Predicate p -> 
            (*fixme: look up definition:*)
            List.fold_left c acc p.args

    ) dft_temp_f_prop
    in

    let type_fol_expr = map_fol_pred @@ map_expr (Fun.id) (fun (id,t) -> 
        id,(t,Bindings.find id bindings))
    in

    let type_prog_expr = map_fol_pred @@ map_expr (Fun.id) (
        fun (id,()) -> id,(None,Bindings.find id bindings)
        ) in

    let prog_spec = 

        let type_spec checks = List.map (fun (f_ltl: parsed_temp_spec_t) -> 
            let f_ltl = map_ltl_pred (fun f_fol -> 
                let fol = type_fol_expr f_fol.value in
                let prop = fold_fol_prop checks fol in 
                if is_static_prop prop then 
                    Format.asprintf "temporal formula %a does not contain any program variables" 
                        Printer.(pp_fol (pp_pred (pp_exp (fun fmt (s,(t,_)) -> pp_hist fmt (s,t)))) pp_base_ty) fol |> failwith
                ;
                mk_labeled prop fol
            ) f_ltl in
            let prop = fold_ltl (fun acc _ -> acc) (fun acc fol -> join_temp_f_prop acc fol.label) dft_temp_f_prop f_ltl in 
            (* todo : static formula -> probable user error *)
            mk_labeled prop f_ltl
        ) 
        in
        {requires = type_spec requires_checks p.prog_spec.requires  ; 
        ensures = type_spec ensures_checks p.prog_spec.ensures ;
        data = ()}

    and prog_setup = Option.map (fun s -> 
        let setup_ensures = List.map type_prog_expr s.setup_ensures
        and setup_body = List.map (map_stmt Fun.id (fun (id,()) -> id,(Bindings.find id bindings)) type_prog_expr) s.setup_body in
        {setup_ensures; setup_body}

    )
    p.prog_setup 
    and prog_main = 
        let main_body = 
            List.map (map_stmt Fun.id (fun (id,()) -> id,(Bindings.find id bindings)) type_prog_expr) p.prog_main.main_body
        and main_loop_inv = List.map type_prog_expr p.prog_main.main_loop_inv in
        {main_body; main_loop_inv}
    in
    {prog_setup; prog_main; prog_spec; prog_decls={env_variables=bindings}}

