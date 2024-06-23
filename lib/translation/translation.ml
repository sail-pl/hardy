(* module A = Automaton *)
open HardySyntax.Syntax
open HardySyntax.Fol
open Ltl2buchi
open TranslateUtils
open HardyExternals.Ltl2ba
open Generation
open Why3
open Why3gen

let translate_program (i : info) (p : program) : P.mlw_file =
  let uses = [ [ "int"; "Int" ]; [ "ref"; "Ref" ] ] in

  let a = product_automaton i p.prog_spec.requires p.prog_spec.ensures in

  let decls = generate_declarations p.prog_env in

  let setup = make_setup p.prog_setup in

  let body = translate_statements pterm_of_fol p.prog_main.main_body in

  let funs =
    PG.fold_vertex
      (fun v l ->
        (let in_e = PG.pred_e a v in
         let out_e = PG.succ_e a v in
         (* provide init post-condition for first node *)
         let extra_req =
           if not @@ PG.is_start_node v then None
           else
             Option.fold p.prog_setup ~none:(Some true_fol) ~some:(fun x ->
                 Some (fold_mjoin Fun.id and_fol true_fol x.setup_ensures))
         in

         let specs =
           make_prod_spec p.prog_env.env_input in_e out_e extra_req |> to_spec
         in
         (* if two or more transition share the same input, but with different outputs,
             we naively generate one spec per involved transition *)
         List.mapi
           (fun i s ->
             let open Format in
             let index = if i <> 0 then sprintf "_%i" i else "" in
             let id = PG.(id_of_vertex (V.label v)) ^ index in
             mk_fun id s body)
           specs)
        @ l)
      a []
  in

  let m =
    ( H.ident "Program",
      List.fold_left
        (fun l u -> H.use ~import:false u :: l)
        (decls @ (setup :: funs))
        uses )
  in
  Ptree.Modules [ m ]
