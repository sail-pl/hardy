open Formulas
open MiddleParser.NcSyntax
open HardyMisc.Utils
open HardyMisc.Why3Utils
open Why3

(* msat *)
module Sat = Msat_sat
module E = Sat.Int_lit (* expressions *)
module F = Msat_tseitin.Make (E)

let task_of_bform (b : string bform) : Task.task =
  let rec aux (task : Task.task) (vars : Term.Sls.t) :
      string bform -> Term.Sls.t * Term.term * Task.task = function
    | True -> (vars, Term.t_true, task)
    | False -> (vars, Term.t_false, task)
    | Atom a ->
        let vars, ps, task =
          try
            ( vars,
              Term.Sls.(
                filter (fun v -> String.equal v.ls_name.id_string a) vars
                |> choose),
              task )
          with Not_found ->
            let ps = Term.create_psymbol (Ident.id_fresh a) [] in
            let task = Task.add_param_decl task ps in
            (Term.Sls.add ps vars, ps, task)
        in
        (vars, Term.ps_app ps [], task)
    | And (b1, b2) ->
        let vars, b1, task = aux task vars b1 in
        let vars, b2, task = aux task vars b2 in
        (vars, Term.t_and b1 b2, task)
    | Or (b1, b2) ->
        let vars, b1, task = aux task vars b1 in
        let vars, b2, task = aux task vars b2 in
        (vars, Term.t_or b1 b2, task)
    | Not b ->
        let vars, b, task = aux task vars b in
        (vars, Term.t_not b, task)
  in
  let _, t, task = aux None Term.Sls.empty b in
  let goal = Decl.create_prsymbol (Ident.id_fresh @@ "accept_bform") in
  Task.add_prop_decl task Decl.Pgoal goal t

let atomic_disjunction forms =
  let l =
    List.filter_map
      (function
        | LTLM_False -> Some False
        | LTLM_True -> Some True
        | LTLM_A a -> Some (Atom a)
        | LTLM_NotA a -> Some (Not (Atom a))
        | _ -> None)
      (NNFSet.to_list forms)
  in
  fold_mjoin Fun.id (fun x y -> Or (x, y)) True l

let is_valid_w3 w3 ((prover, driver) : Whyconf.config_prover * Driver.driver)
    (l : string bform) (disj : NNFSet.t) : bool =
  let f = l <-> atomic_disjunction disj in

  let t = task_of_bform f in
  Format.printf "checking validity of %a" Pretty.print_task t;
  let res =
    Call_provers.wait_on_call
      (Driver.prove_task ~command:prover.Whyconf.command ~config:w3.main
         ~limits:Call_provers.{ empty_limits with limit_time = 10. }
         driver t
        : Call_provers.prover_call)
  in
  match res.pr_answer with
  | Valid -> true
  | Invalid | Unknown _ -> false
  | _ ->
      Format.printf "unexpected output: %a" Call_provers.print_prover_answer
        res.pr_answer;
      failwith "abort"

let is_sat_msat (module Atom : Atom.S) (c : string bform) : bool =
  let rec create_clause : string bform -> F.t = function
    | True -> F.f_true
    | False -> F.f_false
    | Atom a -> Atom.atom_id_to_int a |> E.make |> F.make_atom
    | And (b1, b2) -> F.make_and [ create_clause b1; create_clause b2 ]
    | Or (b1, b2) -> F.make_or [ create_clause b1; create_clause b2 ]
    | Not b -> F.make_not (create_clause b)
  in
  let is_sat c =
    let solver = Sat.create () in
    Sat.assume solver (F.make_cnf c) ();
    match Sat.solve solver with
    | Sat _st ->
        (* Format.printf "found model for %a@," F.pp c; *)
        (* st.iter_trail
             (fun a -> Format.printf "(%a,%b) " E.pp a (st.eval a))
             (fun _ -> ());
           Format.print_space ();
           Format.print_space (); *)
        true
    | Unsat _st ->
        (* Format.printf "found unsatisfiable clause '%a'@," F.pp c; *)
        (* Format.printf "Proof Steps: ";
           Sat.Proof.fold
             (fun _ node ->
               let step = Sat.Proof.expl node.step in
               Format.printf " @[<hov 2> %s %a @] @," step Sat.Clause.pp
                 node.conclusion)
             () (st.get_proof ()); *)
        false
  in
  is_sat (create_clause c)
