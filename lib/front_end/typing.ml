open FrontParser.Program
open HardyMisc.Utils
open Syntax.Shared
open Syntax.Program
open Syntax.Ltl
open Syntax.Fol

let reserved_words = ["result" ; "old" ;  "list" ; "int"] (* todo: add more*)

let fail_if_reserved s = if List.mem s reserved_words then Format.sprintf "'%s' is a reserved word" s |> failwith else s

let fail_if_no_bindings id b = match Bindings.find_opt id b with
    | Some x -> x
    | None -> Format.sprintf "variable '%s' has not been declared" id |> failwith 

let type_pgrm (p : parsed_program) : frontend_program = 
    let bindings : (cat_ty * base_ty option) Bindings.t = 
        let open Bindings in
        let check_dup = fun x (cat1,_) (cat2,_) -> 
            Format.asprintf "duplicate %a and %a variable %s" Printer.pp_cat_ty cat1 Printer.pp_cat_ty cat2 x |> failwith
        in

        let inputs = List.map (fun (s,t) -> (fail_if_reserved s,(Input, Some t))) p.prog_decls.env_input |> of_list
        and outputs = List.map (fun (s,t) -> (fail_if_reserved s,(Output, Some t))) p.prog_decls.env_output |> of_list
        and states = List.map (fun (s,t) -> (fail_if_reserved s,(State, Some t))) p.prog_decls.env_variables |> of_list in
        
        union check_dup inputs outputs |> fun io -> union check_dup io states
    in

    let [@warning "-4"] requires_checks = fun acc e -> match e.value with 
        | Var (_,(None,(Output,_))) -> 
            failwith "output variables within 'relies on' spec cannot mention current output, only past"
        | Var (_,(inst,(Input,_))) ->
            {acc with mentions_input = true; mentions_history = Option.is_some inst}
        | Var (_,(inst,(Output,_))) ->
            {acc with mentions_output = true; mentions_history = Option.is_some inst}                       
        | Var (_,(_,(State,_))) ->
            failwith "'relies on' spec cannot mention state variables"
        | _ -> acc
        
    and [@warning "-4"] ensures_checks = (fun acc e -> match e.value with 
                | Var (_,(inst,(Input,_))) ->
                    {acc with mentions_input = true; mentions_history = Option.is_some inst}
                | Var (_,(inst,(Output,_))) ->
                    {acc with mentions_output = true; mentions_history = Option.is_some inst}                       
                | Var (_,(inst,(State,_))) ->
                    {acc with mentions_state = true; mentions_history = Option.is_some inst}      
                | _ -> acc
        )     
    and fold_fol_prop c = fold_fol (fun acc _ -> acc) (fun acc -> function
        | Atom e -> fold_expr c acc e
        | Predicate p -> 
            (*fixme: look up definition:*)
            List.fold_left c acc p.args

    ) dft_temp_f_prop
    in

    let type_fol_expr = 
        let set_expr_type b = map_expr (Fun.id) (fun (id,t) -> id,(t,fail_if_no_bindings id b))
        in

        let [@warning "-4"] rec aux b = 
            (fun f -> match f.value with
            | ForallPrev q -> 
                let b = Bindings.add q.binder (Local, snd @@ fail_if_no_bindings q.h_var bindings) b in
                let f = map b q.f in
                {f with value = ForallPrev {q with f}}
            | ExistsPrev q -> 
                let b = Bindings.add q.binder (Local, snd @@ fail_if_no_bindings q.h_var bindings) b in
                let f = map b q.f in
                {f with value = ExistsPrev {q with f}}

            | _ -> map b f
            ) 
        and map b = map_fol (aux b) (map_pred @@ set_expr_type b) Fun.id
        in            
        aux
    in

    let type_prog_expr = map_fol_pred @@ map_expr (Fun.id) (
        fun (id,()) -> id,(None,fail_if_no_bindings id bindings)
        ) in

    let prog_spec = 
        let type_spec checks = List.map (fun (f_ltl: parsed_temp_spec_t) -> 
            let f_ltl = map_ltl_pred (fun f_fol -> 
                let fol = type_fol_expr bindings f_fol.value in
                let prop = fold_fol_prop checks fol in 
                if is_static_prop prop then 
                    Format.asprintf "temporal formula %a does not contain any program variables" 
                        Printer.(pp_fol (pp_pred (pp_exp (fun fmt (s,(t,_)) -> pp_hist fmt (s,t)))) (Format.pp_print_option pp_base_ty)) fol |> failwith
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

