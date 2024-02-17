open ArduinoSyntax.Syntax
open Why3
open TranslateUtils


let rec translate_fol ({value=f;loc}:fol) : Ptree.term = 
  let loc = Loc.extract loc in 
  let open H in 
  let open P in 
  match f with
  | FOL_True -> term ~loc Ttrue
  | FOL_False -> term ~loc Tfalse
  | Pred p -> translate_term p 
  | FOL_Unary (uop,t) -> begin match uop with Not -> Tnot (translate_fol t) |> term ~loc end
  | FOL_Binary (t1,bop,t2) -> 
    let t1 = translate_fol t1 in 
    let t2 = translate_fol t2 in
    let bop = begin match bop with
    | And -> Dterm.DTand
    | Or -> Dterm.DTor
    | Arrow -> Dterm.DTimplies
    | Equiv -> Dterm.DTiff
    | Xor -> failwith "todo xor"
    | Arithm _ -> failwith "todo Arithm"
    end in
    Tbinop (t1, bop, t2) |> term ~loc
  | Forall (v,f) -> Tquant (DTforall,  one_binder v, [], (translate_fol f)) |> term ~loc
  | Exists (v,f) ->  Tquant (DTexists,  one_binder v, [], (translate_fol f)) |> term ~loc



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
  | FOL f ->  translate_fol f
  | _ -> failwith "unhandled"

  
  let make_setup (s:setup option) = Option.bind s @@ fun s ->
    translate_statements translate_fol s.setup_body |> Option.some

  (* fixme : go back to bottom-up style *)
  let translate_program (p : program) : P.mlw_file = 
    let open H in 
    let uses = [["int";"Int"];["ref";"Ref"];["option";"Option"];["list";"List"];["list";"Length"]] in
  
    let sp_pre = [translate_formula p.prog_requires] in
    let inv = translate_formula p.prog_ensures in
    let sp_post = [Loc.dummy_position, [pat Pwild, inv]] in
    let spec = Ptree_helpers.{ empty_spec with sp_pre ; sp_post ; sp_diverge = true } in
  
    let decls = generate_declarations p.prog_env in
    let setup = make_setup p.prog_setup |> fun x -> Option.value x ~default:(expr unit_val)in
    let body = translate_statements translate_fol p.prog_main.main_body in
    let loop = make_loop body [inv] in
  
    let stmt = Esequence (setup, loop) |> expr in
  
    let main : P.decl =   
      Efun ([], None, pat Pwild, Ity.MaskVisible, spec, stmt) 
      |> expr 
      |> fun m -> P.Dlet (ident "main", false, Expr.RKnone, m)
    in
  
    let m = (H.ident "Program", List.fold_left (fun l u -> H.use ~import:false u :: l) (decls@[main]) uses) in
    Ptree.Modules [m]