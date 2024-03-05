
module A = Automaton 
open ArduinoSyntax.Syntax
open ArduinoSyntax.AutomatonSyntax
open TranslateLTL
open TranslateUtils
open Why3
open Why3gen 

let make_spec  (_bt: buchi_type)  (_input : (string*ty) list) (_in_e : Buchi.E.t list) (_out_e : Buchi.E.t list) (_init_post: fol option): Ptree.spec list =  
let open Ptree_helpers in
(* TODO : specialized version for require/ensure automaton *)
List.map (fun h -> 
let sp_pre = List.map pterm_of_fol h.requires in
let post = List.map (fun e -> pat Pwild,pterm_of_fol e) h.ensures  in
{Ptree_helpers.empty_spec with sp_pre ; sp_post=[Loc.dummy_position, post]}
) []


let translate_program (i:info) (p : program) : P.mlw_file = 
  let uses = [["int";"Int"];["ref";"Ref"]] in

  let a = make_automaton i (p.prog_spec.requires,p.prog_spec.ensures) in

  let decls = generate_declarations p.prog_env in
  
  let setup = make_setup p.prog_setup in

  let body = translate_statements pterm_of_fol p.prog_main.main_body in


  let generate_funs (type a) (type edge) (module B : A.BuchiSig with type t = a and type E.t = edge) (a : B.t)
  (mk_specs: (state*ty) list -> edge list -> edge list -> fol option -> Ptree.spec list) :
    Ptree.decl list =
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
    | Right (a,m) -> generate_funs m a (fun x y z t -> (to_spec (make_prod_spec x y z t)))
  in

  let m = (H.ident "Program", List.fold_left (fun l u -> H.use ~import:false u :: l) (decls@setup::funs) uses) in 
  Ptree.Modules [m]