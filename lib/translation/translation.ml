module A = Automaton
open ArduinoSyntax.Syntax
(* open ArduinoSyntax.PromelaSyntax *)
open TranslateLTL
open TranslateUtils
open Ltl2ba
open Why3
open Why3gen

let translate_program (i : info) (p : program) : P.mlw_file =
  let uses = [ [ "int"; "Int" ]; [ "ref"; "Ref" ] ] in

  let a = make_automaton i (p.prog_spec.requires, p.prog_spec.ensures) in

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
           Option.(
             bind p.prog_setup @@ fun x ->
             if PG.is_start_node v then x.setup_ensures else None)
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
