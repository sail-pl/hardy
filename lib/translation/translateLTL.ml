open TranslateUtils
open ArduinoSyntax.Syntax
open Why3


let atomic_bindings : (int,fol) Hashtbl.t = Hashtbl.create 100
let cnt = ref 0
let add_atom (f:fol) = 
  let curr_cnt = !cnt in 
  Hashtbl.add atomic_bindings curr_cnt f; 
  incr cnt; 
  curr_cnt


(* let rec translate_ltl (f:ltl) : Core.Ltl.formula = 
  let open Core.Ltl in

  let translate_binop : ltl_binary -> bop = function
  | Until -> Until
  | Release -> Release
  | LTL_BArithm Arrow -> Implies
  | LTL_BArithm Or -> Or
  | LTL_BArithm And -> And
  | _ -> failwith "unsupported bop"
  in
  let translate_unop : ltl_unary -> uop = function
  | Next -> Next
  | Always -> Globally
  | Eventually -> Finally
  | LTL_UArithm Not -> Not
  | WeakNext -> failwith "unsupported unop"
  in

  match f.value with
  | LTL_True -> Bool true
  | LTL_False -> Bool false
  | LTL_Pred p -> Prop (Format.sprintf "f_%i" @@ add_atom p)
  | LTL_Binary (f1,op,f2) -> 
    let f1 = translate_ltl f1 in
    let f2 = translate_ltl f2 in
    Bop (f1, translate_binop op, f2)
  | LTL_Unary (op,f) ->
    let f = translate_ltl f in
    Uop (translate_unop op,f)
  | Last | End -> failwith "unsupported last,end" *)


  let uses = [
    ["int";"Int"];
    ["ref";"Ref"];
  ]

  (* let translate_spec ?dbg:s = function
  | LTL f -> let f = translate_ltl f in
            Option.iter (fun name -> Format.fprintf Format.std_formatter "%s formula : %s\n" name @@ Core.Ltl.to_string f) s;
            f
            |> Core.Ltl.nnf
            |> Ltl2ba.translate  
  | _ -> failwith "not an LTL formula" *)


let mk_fun name spec body = 
  let open P in 
  let open H in
  Efun ([], None, pat Pwild, Ity.MaskVisible, spec, body) 
  |> expr 
  |> fun m -> P.Dlet (ident name, false, Expr.RKnone, m)

let make_setup (setup : setup option) = 
  let open H in
  match setup with
  | None ->  mk_fun "start" empty_spec (expr unit_val)
  | Some s ->
    begin
      let bdy = translate_statements TranslateFOL.translate_fol s.setup_body in
      let spec = match s.setup_ensures with
        | None -> empty_spec
        | Some f -> 
            {empty_spec with sp_post=[Loc.dummy_position, [(pat Pwild, TranslateFOL.translate_formula f)]] } 
        in
          mk_fun "start" spec bdy   
    end

let translate_program (_dir:string) (p : program) : P.mlw_file = 
  (* let open H in  *)

  let uses = [["int";"Int"];["ref";"Ref"]] in

  (* let pre_automata = translate_spec ?dbg:(Some "rely") p.prog_requires in
  let post_automata = translate_spec ?dbg:(Some "guarantee") p.prog_ensures in

  Ltl2ba.print_automata Filename.(concat dir "rely.dot") pre_automata;
  Ltl2ba.print_automata Filename.(concat dir "guarantee.dot") post_automata;

  let _sp_pre = [pre_automata] in
  let _sp_post = [Loc.dummy_position, [pat Pwild, post_automata]] in *)

  (* add one lemma per edges *)
  (* Core.Automata.TransBuchi.iter_vertex (fun v -> Core.Automata.TransBuchi.)
  Core.Algorithm.states_to_string  *)


  let spec = H.empty_spec in
  let decls = generate_declarations p.prog_env in
  
  let setup = make_setup p.prog_setup in

  let body = translate_statements TranslateFOL.translate_fol p.prog_main.main_body in

  
  let states = [setup;mk_fun "test" spec body] (* map on automata states *) in

  let m = (H.ident "Program", List.fold_left (fun l u -> H.use ~import:false u :: l) (decls@states) uses) in 
  Ptree.Modules [m]