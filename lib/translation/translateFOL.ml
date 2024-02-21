open ArduinoSyntax.Syntax
open Why3
open TranslateUtils


let make_loop (body:Ptree.expr) inv = 
  P.Ewhile (H.expr Etrue,inv,[], body) |> H.expr

  let uses = [
    ["int";"Int"];
    ["ref";"Ref"];
    ["option";"Option"];
    ["list";"List"];
    ["list";"Length"];
  ]

  let translate_formula f = match f with 
  | FOL f -> pterm_of_fol f
  | _ -> failwith "unhandled"


  let combine_fol f1 f2 = match f1,f2 with | FOL f1,FOL f2 -> FOL {loc=f1.loc ; value=(FOL_Binary (f1,And,f2))} | _ -> failwith "not fol"

  
  let make_setup (s:setup option) = Option.bind s @@ fun s ->
    translate_statements pterm_of_fol s.setup_body |> Option.some

  (* fixme : go back to bottom-up style *)
  let translate_program _ (p : program) : P.mlw_file = 
    let open H in 
    let uses = [["int";"Int"];["ref";"Ref"];["option";"Option"];["list";"List"];["list";"Length"]] in
  
    let sp_pre = [translate_formula p.prog_spec.requires] in
    let inv = translate_formula p.prog_spec.ensures in
    let sp_post = [Loc.dummy_position, [pat Pwild, inv]] in
    let spec = Ptree_helpers.{ empty_spec with sp_pre ; sp_post ; sp_diverge = true } in
  
    let decls = generate_declarations p.prog_env in
    let setup = make_setup p.prog_setup |> fun x -> Option.value x ~default:(expr unit_val)in
    let body = translate_statements pterm_of_fol p.prog_main.main_body in
    let loop = make_loop body [inv] in
  
    let stmt = Esequence (setup, loop) |> expr in
  
    let main : P.decl =
      Efun ([], None, pat Pwild, Ity.MaskVisible, spec, stmt) 
      |> expr 
      |> fun m -> P.Dlet (ident "main", false, Expr.RKnone, m)
    in
  
    let m = (H.ident "Program", List.fold_left (fun l u -> H.use ~import:false u :: l) (decls@[main]) uses) in
    Ptree.Modules [m]