module L = Lexing
module A = Automaton 

open  TranslateUtils
open ArduinoSyntax.Syntax
open ArduinoSyntax.AutomatonSyntax
open Why3

module Atoms = Atom()
module Buchi = A.Buchi(Atoms)
module DotG = A.BuchiDot(Buchi)
module PG = A.BuchiProd(Buchi)(Atoms)
module DotPG = A.BuchiDot(PG)


let compute_automaton (f:string) (i:info) (output_file:string->string) =
  (* ltl3ba presentation : https://pdfs.semanticscholar.org/6d7d/04f5255cccf22108468747037be889e3f535.pdf *)
  let open ArduinoParser.Parsing in
  let never_file = output_file ".never" in 

  let cmd = Filename.quote_command i.ltl2baPath ["-f"; f] ~stdout:never_file ~stderr:(never_file ^ ".err") in

  if i.verbose then Format.printf "ltl2ba command line : %s" cmd;

  let ret = Sys.command @@ Filename.quote_command i.ltl2baPath ["-f"; f] ~stdout:never_file ~stderr:(never_file ^ ".err") in
  
  
  if ret <> 0 then failwith Format.(sprintf "non-0 exit-code (%i) from ltl2ba" ret);

  let auto = parse_automaton never_file |> Buchi.create in

  Out_channel.with_open_text (output_file ".dot")  (fun o -> DotG.output_graph o auto) ;   
  auto 


let string_of_ltl_full = string_of_ltl (fun p -> Atoms.add p |> snd)
let string_of_ltl_short = string_of_ltl (fun p -> Atoms.add p |> fst)
    

let mk_fun name spec body = 
  let open P in 
  let open H in
  Efun ([], None, pat Pwild, Ity.MaskVisible, spec, body) 
  |> expr 
  |> fun m -> P.Dlet (ident name, false, Expr.RKnone, m)


let make_setup (setup : setup option) = 
  let open H in
  match setup with
  | None ->  mk_fun "setup" empty_spec (expr unit_val)
  | Some s ->
    begin
      let bdy = translate_statements pterm_of_fol s.setup_body in
      let spec = match Option.(map TranslateFOL.translate_formula s.setup_ensures)  with
        | None -> empty_spec
        | Some f -> 
            {empty_spec with sp_post=[Loc.dummy_position, [(pat Pwild,f)]] } 
        in
          mk_fun "setup" spec bdy   
    end


let ltl_conjunction f1 f2 = match f1,f2 with 
  | Some (LTL f1),Some (LTL f2) -> Some (LTL {loc=f1.loc ; value=(LTL_Binary (f1,LTL_BArithm And,f2))})
  | Some (LTL f),None | None,Some (LTL f) -> Some (LTL f)
  | None,None -> None
  | _ -> failwith "not a LTL formula"


type buchi_type = Requires | Ensures 

let make_automaton info (req,ens) : 
  (
    Buchi.t * buchi_type * (module A.BuchiSig with type t =Buchi.t and type E.t = Buchi.edge), 
    PG.t * (module A.BuchiSig with type t = PG.t and type E.t = PG.edge)
  ) 
  Either.t = 
  
  let output_file name ext = Filename.(concat info.outdir (name ^ ext)) in

  let translate_spec (name:string) = function
  | LTL f -> 
      let f_str = string_of_ltl_full f in
      if info.verbose then 
        begin
        let f_str_short = string_of_ltl_short f in 
        Format.printf "\n %s formula : \n%s\n" name f_str_short;
        end;
      compute_automaton f_str info (output_file name)

  | _ -> failwith "not a LTL formula"
  in

  let rely_a = Option.map (translate_spec "rely") req in
  let guarantee_a = Option.map (translate_spec "guarantee") (ltl_conjunction req ens) in

  match rely_a,guarantee_a with
  | None,None ->  
    Left (compute_automaton "true" info (output_file "dummy"), Ensures,(module Buchi))
  | Some a,None -> Left (a,Requires,(module Buchi))
  | None,Some a -> Left (a,Ensures, (module Buchi))
  | Some ra, Some ga -> 
    let prod_a = PG.create (ra,ga) in 
    Out_channel.with_open_text (output_file "product" ".dot")  (fun o -> DotPG.output_graph o prod_a);
    Right (prod_a,(module PG))


(* create a map binding the exit-arc rely formula to all its guarantee ones *)
module M = Map.Make(
    struct type t = AS.bform
    let compare e1 e2 = String.compare (e1 |> string_of_bform Fun.id) (e2 |> string_of_bform Fun.id)
end) 


let make_prod_spec  (input : (string*ty) list) 
  (in_e : PG.E.t list) (out_e : PG.E.t list) (init_post: requires option): Ptree.spec list =  
  let in_e_hd,in_e_tl = match in_e with hd::tl -> hd,tl | _ -> failwith "all paths reachable -> exists pred(state)" 
  in

  let open H in 
  let open P in 
  let to_fol = fol_of_bform (fun a -> Atoms.get a |> snd) in

  let init_post  =
      Option.map (function FOL f -> f | _ -> failwith "setup ensures is not a fol") init_post
  in

  let combine_fol f1 op f2 = mk_dummy_loc (FOL_Binary (f1, op, f2)) in

  (* group exit arc by their first component (requires) *)
  let m = List.fold_left (fun m e -> let l = PG.E.label e in M.add_to_list l.requires l.ensures m) M.empty out_e in

  let specs = M.fold (fun k (d: bform list) s -> 
    let d_hd,d_tl = match d with hd::tl -> hd,tl | _ -> failwith "ω-automaton  -> exists succ(state)" 
    in

    let requires = [

      (* disjunction of all entry-arcs post-condition *)
      let exists = List.fold_left 
        (fun acc e -> combine_fol (to_fol (PG.E.label e).ensures) Or acc) 
        (to_fol (PG.E.label in_e_hd).ensures) 
        in_e_tl 
        |> fun f -> Exists (input, f) |> mk_dummy_loc
      in

      (* if initial node, add ensures from setup  *)
      let disj = Option.fold init_post ~none:exists ~some:(fun i -> combine_fol i Or exists) in

      (* finally, factorize the result by the exit-arc pre-condition *)
      combine_fol disj And (to_fol k)
    ] in
    let ensures = [
        (* disjunction of exit-arc post-condition sharing the same pre-condition *)
        List.fold_left (fun acc f -> combine_fol acc Or (to_fol f)) (to_fol d_hd) d_tl
      ]
    in
      {requires;ensures}::s
    ) m [] 
  in

  List.map (fun h -> 
    let sp_pre = List.map pterm_of_fol h.requires in
    let post = List.map (fun e -> pat Pwild,pterm_of_fol e) h.ensures  in
    {H.empty_spec with sp_pre ; sp_post=[Loc.dummy_position, post]}
  ) specs
  


let make_spec  (_bt: buchi_type)  (_input : (string*ty) list) (_in_e : Buchi.E.t list) (_out_e : Buchi.E.t list) (_init_post: requires option): Ptree.spec list =  
    let open H in
    (* TODO : specialized version for require/ensure automaton *)
  List.map (fun h -> 
    let sp_pre = List.map pterm_of_fol h.requires in
    let post = List.map (fun e -> pat Pwild,pterm_of_fol e) h.ensures  in
    {H.empty_spec with sp_pre ; sp_post=[Loc.dummy_position, post]}
  ) []



let translate_program (i:info) (p : program) : P.mlw_file = 
  let uses = [["int";"Int"];["ref";"Ref"]] in

  let a = make_automaton i (p.prog_spec.requires,p.prog_spec.ensures) in

  let decls = generate_declarations p.prog_env in
  
  let setup = make_setup p.prog_setup in

  let body = translate_statements pterm_of_fol p.prog_main.main_body in


  let generate_funs (type a) (type edge) (module B : A.BuchiSig with type t = a and type E.t = edge) (a : B.t)
  (mk_specs: (state*ty) list -> edge list -> edge list -> requires option -> Ptree.spec list) =
    B.fold_vertex (fun v l -> (
      let in_e = B.pred_e a v in
      let out_e =  B.succ_e a v in
  
      (* provide init post-condition for first node *)
      let extra_req = Option.(bind p.prog_setup @@ fun x -> if B.is_start_node v then x.setup_ensures else None) in
    
      let specs = mk_specs p.prog_env.env_input in_e out_e extra_req in
    
      (* if two or more transition share the same input, but with different outputs,
          we naively generate one spec per involved transition  *)
      List.mapi (fun i s -> 
        let open Format in 
        let index = if i <> 0 then sprintf "_%i" i else "" in
        let id = B.(id_of_vertex (V.label v)) ^ index in
        mk_fun id s body
      ) specs
    ) @ l
    ) a [] 
  in

  let funs = match a with
    | Left (a,bt,m) -> generate_funs m a (make_spec bt)
    | Right (a,m) -> generate_funs m a make_prod_spec
  in

  let m = (H.ident "Program", List.fold_left (fun l u -> H.use ~import:false u :: l) (decls@setup::funs) uses) in 
  Ptree.Modules [m]