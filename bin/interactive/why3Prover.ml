open HardyFrontEnd
open HardyMisc.Utils
open Why3
open Syntax
open Syntax.Program
module P = Why3.Ptree
module Why3Utils = HardyBackEnd.Why3_back.Utils 


module M(BaseSpec : SIMP_TYPE)(T: SIMP_TYPE )(TriplesType : SIMP_TYPE)
  : Sig.S with 
    type program = (T.t, unit, BaseSpec.t, Shared.ty, Shared.ty env) program * P.mlw_file and 
    type triples = TriplesType.t


  = struct
  (* module BU = Buchi.BuchiSig.Utils (B) *)

  type nonrec program = (T.t, unit, BaseSpec.t, Shared.ty, Shared.ty env) program * P.mlw_file
  type proof_result = Success | Failure of string
  (* type automaton = B.t
  type node = B.vertex *)
  type proof_state = int

  type triples = TriplesType.t

  type backend_state = {
    prover : Whyconf.config_prover;
    driver : Driver.driver;
    w3 : Why3Utils.w3;
    modules : Why3.Pmodule.pmodule Why3.Wstdlib.Mstr.t;
  }

  type vc = Task.task

  let init_backend ((_,modules) : program) =
    let open Why3Utils in
    let w3 = init_why3 () in
    let modules =
      try
        Why3.Typing.type_mlw_file w3.env [] "???" modules 
      with Why3.Loc.Located (loc, e) -> Why3.Loc.error ~loc e
    in
    let prover, driver = get_alt_ergo w3 in
    { prover; driver ; w3; modules}

  let get_vcs status (_ : triples) : vc list =
  
    Wstdlib.Mstr.fold
      (fun _mname m acc ->
        List.rev_append (Task.split_theory m.Pmodule.mod_theory None None) acc)
      status.modules []
    |> List.rev

  let prove status (vc : vc) =
    (* Driver.print_task status.driver Format.std_formatter vc; *)
    let goal = Task.task_goal vc in
    (* Format.printf "checking goal \"%s\"@." goal.pr_name.id_string; *)
    let open Call_provers in
    (* Format.printf "%s" status.prover.Whyconf.command; *)
    let res =
      wait_on_call
        (Driver.prove_task ~command:status.prover.Whyconf.command
           ~config:status.w3.main
           ~limits:{ empty_limits with limit_time = 2. }
           status.driver vc
          : prover_call)
    in
    let g_m = Format.sprintf "%s: %s" goal.pr_name.id_string in
    match res.pr_answer with
    | Valid -> Success
    | Invalid -> Failure (g_m "invalid")
    | Timeout -> Failure (g_m "timeout")
    | OutOfMemory -> Failure (g_m "Out of Memory")
    | StepLimitExceeded -> Failure "max step reached"
    | Unknown msg | Failure msg | HighFailure msg -> Failure (g_m msg)
end
