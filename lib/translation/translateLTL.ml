module L = Lexing
module A = Automaton 

open  TranslateUtils
open ArduinoSyntax.Syntax
open ArduinoSyntax.AutomatonSyntax
open Why3

(* key is a hash of fol, value is a short name for fol + fol itself*)
let atomic_bindings : (int, string*fol) Hashtbl.t = Hashtbl.create 100

let cnt = ref 0

let rec determ_exp (e:expr) : expr =
  let value = 
    match e.value with
    | BinOp (e1,op,e2) -> let e1 = determ_exp e1 and e2 = determ_exp e2 in BinOp (e1,op,e2)
    | _ as x -> x
  in
  {value;loc=None}

(* 2 formulas are equals if they are syntactically the same modulo their position *)
let rec determ_fol (f:fol) : fol = 
    let value = 
      match f.value with 
      | Pred p -> Pred (determ_exp p)
      | FOL_Unary (op,f) -> let f = determ_fol f in FOL_Unary (op,f)
      | FOL_Binary (f1, op, f2) -> 
        let f1 = determ_fol f1 and f2 = determ_fol f2 in FOL_Binary (f1,op,f2)
      | Forall (x,f) -> let f = determ_fol f in Forall (x,f)
      | Exists (x,f) -> let f = determ_fol f in Exists (x,f)
      | _ as x -> x
    in
    {value;loc=None}

let add_atom (f:fol) = 
  let label =  Format.sprintf "f_%i" in 

  (* we must get the same atom if the formulas are syntactically equal*)
  let key = Hashtbl.hash (determ_fol f) in 
  
  match Hashtbl.find_opt atomic_bindings key with
  | None -> 
    let short_name = "F" ^ string_of_int !cnt in
    Hashtbl.add atomic_bindings key (short_name,f);
    incr cnt;
    short_name,label key
  | Some (sn,_) ->
      sn,label key

let get_atom (s:string) = let k = String.(sub s 2 (length s - 2) |> int_of_string) in Hashtbl.find atomic_bindings k 


let sub_atom_in_str f = 
  let open Str in 
  let r = regexp {|f_\([0-9]+\)|} in
  global_substitute r (fun m -> matched_string m |> f) 


let subst_atom = sub_atom_in_str (fun s -> 
  let _,inv = get_atom s in
  string_of_fol inv
)

let acceptant v = List.hd String.(split_on_char '_' v) = "accept" 

let string_of_vertex v = match String.split_on_char '_' v with
| "accept"::[n] -> n (* acceptant state *)
| s::[] -> s (* non-acceptant state *)
| _ as x -> failwith (Printf.sprintf "bad label name : %s" (String.concat "" x )) 

module DotG = Automaton.BuchiDot(A.G)(struct 
  let acceptant = acceptant

  let string_of_vertex = string_of_vertex

  let string_of_edge (f:bform) = string_of_bform subst_atom f

end)

module DotPG = Automaton.BuchiDot(A.PG)(struct 
  let acceptant (l1,l2) = acceptant l1 && acceptant l2
  let string_of_vertex (l1,l2) = Format.sprintf "{pre_%s \n post_%s}" (string_of_vertex l1) (string_of_vertex l2)
  let string_of_edge e = Format.sprintf "requires: %s \n ensures : %s" (e.requires |> string_of_bform subst_atom) (e.ensures |> string_of_bform subst_atom)

end)

  
let compute_automaton (f:string) (i:info) (output_file:string->string) =
  (* ltl3ba presentation : https://pdfs.semanticscholar.org/6d7d/04f5255cccf22108468747037be889e3f535.pdf *)
  let open ArduinoParser.Parsing in
  let never_file = output_file ".never" in 

  let ret = Sys.command Format.(sprintf "%s -f \"%s\" > %s" i.ltl2baPath f never_file) in
  if ret <> 0 then failwith Format.(sprintf "non-0 exit-code (%i) from ltl2ba" ret);

  let auto = parse_automaton never_file |> A.Buchi.create in

  Out_channel.with_open_text (output_file ".dot")  (fun o -> DotG.output_graph o auto) ;   
  auto 


let string_of_ltl_full = string_of_ltl (fun p -> add_atom p |> snd)
let string_of_ltl_short = string_of_ltl (fun p -> add_atom p |> fst)
    

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
  | LTL f1,LTL f2 -> LTL {loc=f1.loc ; value=(LTL_Binary (f1,LTL_BArithm And,f2))} 
  | _ -> failwith "not fol"


let make_automaton info (req,ens) = 
  let output_file name ext = Filename.(concat info.outdir (name ^ ext)) in

  let translate_spec (name:string) = function
  | LTL f -> 
      let f_str = string_of_ltl_full f in
      let f_str_short = string_of_ltl_short f in 
            Format.fprintf Format.std_formatter "\n%s formula : \n%s\n" name f_str_short;
            compute_automaton f_str info (output_file name)

  | _ -> failwith "not an LTL formula"
  in

  let rely_a = translate_spec "rely" req in
  let guarantee_a = translate_spec "guarantee" (ltl_conjunction req ens) in

  let prod_a = A.BuchiProd.create ~rely_a ~guarantee_a in
  Out_channel.with_open_text (output_file "product" ".dot")  (fun o -> DotPG.output_graph o prod_a);
  prod_a  



(* create a map binding the exit-arc rely formula to all its guarantee ones *)
module M = Map.Make(
    struct type t = AS.bform
    let compare e1 e2 = String.compare (e1 |> string_of_bform Fun.id) (e2 |> string_of_bform Fun.id)
end) 


let _ = M.add_to_list

let make_spec (input : (string*ty) list) (in_e : A.PG.E.t list) (out_e : A.PG.E.t list) (init_post: requires option): Ptree.spec list =  
  let open H in 
  let open P in 
  let open A.PG.E in
  let to_fol = fol_of_bform (fun a -> get_atom a |> snd) in

  let init_post : fol = Option.(
      map (function FOL f -> f | _ -> failwith "setup ensures is not a fol") init_post 
      |> value ~default:(mk_dummy_loc FOL_False)
    ) in

  let combine_fol f1 op f2 = mk_dummy_loc (FOL_Binary (f1, op, f2)) in

  (* group exit arc by their first component (requires) *)
  let m = List.fold_left (fun m e -> let l = label e in M.add_to_list l.requires l.ensures m) M.empty out_e in

  let specs = M.fold (fun k (d: bform list) s -> 
      let requires = [

        (* disjunction of all entry-arcs post-condition *)
        let exists = List.fold_left 
          (fun acc e -> combine_fol (to_fol (label e).ensures) Or acc) 
          (mk_dummy_loc FOL_False) in_e 
          |> fun f -> Exists (input, f) |> mk_dummy_loc
        in

        (* if initial node, add ensures from setup  *)
        let disj = combine_fol  init_post Or exists in

        (* finally, factorize the result by the exit-arc pre-condition *)
        combine_fol disj And (to_fol k)
      ] in
      let ensures = [
          (* disjunction of exit-arc post-condition sharing the same pre-condition *)
          List.fold_left (fun acc f -> combine_fol acc Or (to_fol f)) (mk_dummy_loc FOL_False) d
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
  

let translate_program (i:info) (p : program) : P.mlw_file = 
  let uses = [["int";"Int"];["ref";"Ref"]] in

  let a = make_automaton i (p.prog_spec.requires,p.prog_spec.ensures) in

  let decls = generate_declarations p.prog_env in
  
  let setup = make_setup p.prog_setup in

  let body = translate_statements pterm_of_fol p.prog_main.main_body in

  
  
  let funs = A.PG.fold_vertex (fun v l -> (
        let open A.PG in
        let in_e = pred_e a v in
        let out_e =  succ_e a v in

        let first_node = let n1,n2 = V.label v in
         String.(ends_with n1 ~suffix:"init" && ends_with n2 ~suffix:"init") 
        in
        (* provide init post-condition for first node *)
        let extra_req = Option.(bind p.prog_setup @@ fun x -> if first_node then x.setup_ensures else None) in

        let specs = make_spec p.prog_env.env_input in_e out_e extra_req in

        (* if two or more transition share the same input, but with different outputs,
            we naively generate one spec per involved transition  *)
        List.mapi (fun i s -> 
          let open Format in 
          let index = if i <> 0 then sprintf "_%i" i else "" in
          let id = let l1,l2 = V.label v in sprintf "%s_%s%s" (string_of_vertex l1) (string_of_vertex l2) index in 
          mk_fun id s body
        ) specs
      )@l
    ) a []  in

  let m = (H.ident "Program", List.fold_left (fun l u -> H.use ~import:false u :: l) (decls@setup::funs) uses) in 
  Ptree.Modules [m]