open FrontParser
open Ltl_spec
open HardyMisc.Utils
open Syntax.Shared
open Syntax.Ltl
open Syntax.Fol
open FrontSig

let reserved_words = ["result" ; "old" ;  "list" ; "int"] (* todo: add more*)

let fail_if_reserved s = if List.mem s reserved_words then Format.sprintf "'%s' is a reserved word" s |> failwith else s

let fail_if_no_bindings id b = match Bindings.find_opt id b with
    | Some x -> x
    | None -> Format.sprintf "variable '%s' has not been declared" id |> failwith 


module M : Typing with 
    type in_local_spec = parsed_spec_t and
    type in_temp_spec = parsed_temp_spec_t and
    type out_temp_spec = ((temp_f_prop, (InstantSyntax.instant option * Shared.ty), Shared.base_ty) temp_spec_t, temp_f_prop) U.labeled and
    type out_local_spec = base_spec_t

= struct
    type in_temp_spec = parsed_temp_spec_t
    type out_temp_spec = ((temp_f_prop, (InstantSyntax.instant option * Shared.ty), Shared.base_ty) temp_spec_t, temp_f_prop) U.labeled
    (* Instant.instant should always be None, this just allows for uniform processing  *)

    type in_local_spec = parsed_spec_t
    type out_local_spec = base_spec_t
    

  let type_pgrm (p : (in_temp_spec, unit, in_local_spec, unit, Program.parsed_env) Program.program ) :
    (out_temp_spec, unit, out_local_spec, ty, ty Program.env) Program.program = 
    let open Program in
    let bindings : ty Bindings.t = 
        let open Bindings in
        let check_dup = fun x (cat1,_) (cat2,_) -> 
            Format.asprintf "duplicate %a and %a variable %s" Printer.pp_cat_ty cat1 Printer.pp_cat_ty cat2 x |> failwith
        in

        let inputs = List.map (fun (s,t) -> (fail_if_reserved s,(Input, Some t))) p.prog_decls.env_input |> of_list
        and outputs = List.map (fun (s,t) -> (fail_if_reserved s,(Output, Some t))) p.prog_decls.env_output |> of_list
        and states = List.map (fun (s,t) -> (fail_if_reserved s,(State, Some t))) p.prog_decls.env_variables |> of_list in
        
        union check_dup inputs outputs |> fun io -> union check_dup io states
    in

    let [@warning "-4"] requires_checks = fun acc (e:(InstantSyntax.instant option*ty) expr ) -> match e.value with 
        | Var (_,(None,(Output,_))) -> 
            failwith "output variables within temporal assumption cannot mention current output, only past"             
        | Var (_,(_,(State,_))) ->
            failwith "temporal assumption cannot mention state variables"
        | Var (_,(inst,(cat,_))) ->
            join_temp_f_prop (mentions_temp_f_prop cat) {acc with mentions_history = Option.is_some inst}
            
        | _ -> acc

    and [@warning "-4"] ensures_checks = fun acc e -> match e.value with 
        | Var (_,(inst,(cat,_))) -> 
            join_temp_f_prop (mentions_temp_f_prop cat) {acc with mentions_history = Option.is_some inst}
        | _ -> acc

    in
    let [@warning "-4"] rec fold_fol_prop b acc_f f = match f.value with
        | ForallPrev q | ExistsPrev q -> 
            let hvar_cat,hvar_ty = fail_if_no_bindings q.h_var bindings in 
            let b = Bindings.add q.binder (Local, hvar_ty) b in
            aux b (fun acc -> acc_f (join_temp_f_prop (mentions_temp_f_prop hvar_cat) {acc with mentions_history = true})) q.f
        | _ -> aux b acc_f f

        
    and aux b acc_f = fold_fol (fun acc _ -> acc) (fun acc -> function
        | Atom e -> acc_f acc e
        | Predicate p -> 
            (*fixme: look up definition:*)
            List.fold_left acc_f acc p.args

    ) dft_temp_f_prop
    in

    (* https://ocaml.org/manual/5.2/polymorphism.html#ss:explicit-polymorphism*)
    let set_expr_type : 'a 'b. ('a -> 'b) -> ty Bindings.t -> 'a Program.expr -> ('b * ty) Program.expr = fun f b x ->
        map_expr Fun.id (fun (id,t) -> id,(f t,fail_if_no_bindings id b)) x in

    let type_prog_spec f b = fun x -> map_fol_pred (set_expr_type f b) x   in


    let type_fol_expr : 
        (cat_ty * base_ty option) Bindings.t -> 
        (InstantSyntax.instant option, base_ty) fol_t -> 
        (InstantSyntax.instant option * ty, base_ty) fol_t 
    = 
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
        and map b = map_fol (aux b) (map_pred @@ set_expr_type Fun.id b) Fun.id
        in            
        aux
    in

    let type_fun f b =  fun x -> List.map ( (* todo: will need fold when allowing local variables *)
        map_stmt 
            Fun.id 
            (fun (id,()) -> id,(fail_if_no_bindings id b)) 
            (fun id -> fail_if_no_bindings id b |> ignore; id) 
            (type_prog_spec f b)
    ) x in

    let prog_spec : (out_temp_spec list, unit) hoare_triple = 
        let type_spec checks = 
            List.map (fun (f_ltl:parsed_temp_spec_t) : out_temp_spec ->
                let f_ltl : (temp_f_prop, (InstantSyntax.instant option * ty), base_ty) temp_spec_t = 
                    map_ltl_pred (fun f_fol : ((InstantSyntax.instant option * ty, base_ty) fol_t, temp_f_prop) labeled -> 
                        let fol = type_fol_expr bindings f_fol in
                        let prop = fold_fol_prop bindings checks fol
                        in 
                        if is_static_prop prop then 
                            Format.asprintf "temporal formula '%a' does not contain any program variables" 
                                Printer.(pp_fol (pp_pred (pp_exp (fun fmt (s,(t,_)) -> pp_hist fmt (s,t)))) (Format.pp_print_option pp_base_ty)) fol |> failwith
                        ;
                        mk_labeled ~label:prop fol                                                
                    ) f_ltl
                in
                let prop = fold_ltl (fun acc _ -> acc) (fun acc fol -> join_temp_f_prop acc fol.label) dft_temp_f_prop f_ltl in 
                (* todo : static formula -> probable user error *)
                mk_labeled ~label:prop f_ltl
            ) 
        in
        mk_labeled ~label:() {requires = type_spec requires_checks p.prog_spec.value.requires  ; 
        ensures = type_spec ensures_checks p.prog_spec.value.ensures ;
        }

    and prog_setup : (base_spec_t, ty) setup option = 
        Option.map (fun (s : (in_local_spec,unit) setup)  -> 
        let setup_ensures : base_spec_t list = List.map (type_prog_spec (fun () -> None) bindings) s.setup_ensures
        and setup_body : (base_spec_t, ty) stmt list = type_fun (fun () -> None) bindings s.setup_body in
        {setup_ensures; setup_body}

        ) p.prog_setup 
    and prog_main = 
        let main_body = type_fun (fun () -> None) bindings p.prog_main.main_body
        and main_loop_inv = List.map (type_prog_spec (fun () -> None) bindings) p.prog_main.main_loop_inv in
        {main_body; main_loop_inv}
    in
    {prog_setup; prog_main; prog_spec; prog_decls={env_variables=bindings}}
end


