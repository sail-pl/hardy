(** {1 Why3 Utilities} *)

open Why3

type w3 = {
  config : Why3.Whyconf.config;
  main : Why3.Whyconf.main;
  env : Why3.Env.env;
}
(** interface to why3 *)

let init_why3 () : w3 =
  let open Whyconf in
  let config = init_config None in
  let main = get_main config in
  let env = loadpath main |> Env.create_env in
  { config; main; env }

(** basic program printing *)
let print_program p =
  p |> Fun.flip (Mlw_printer.pp_mlw_file ~attr:true) |> Pp.print_in_file

(** alt-ergo prover *)
let get_alt_ergo (w3 : w3) : Whyconf.config_prover * Driver.driver =
  let open Whyconf in
  let alt_ergo : config_prover =
    (* get all provers that are the regular variant of Alt-Ergo *)
    let fp = parse_filter_prover "Alt-Ergo,," in
    let provers = filter_provers w3.config fp in
    if Mprover.is_empty provers then (
      Format.eprintf "Prover Alt-Ergo not installed or not configured";
      exit 1)
    else
      (* Format.printf "Versions of Alt-Ergo found:";
               Whyconf.(Mprover.iter (fun k _ -> Format.printf " %s-%s" k.prover_version k.prover_altern) provers);
         Format.printf "@,"; *)
      (* return one of the versions (todo: get the most recent one) *)
      snd (Mprover.choose provers)
  in
  let driver =
    try Driver.load_driver_for_prover w3.main w3.env alt_ergo
    with e ->
      Format.eprintf "Failed to load driver for alt-ergo: %a"
        Exn_printer.exn_printer e;
      exit 1
  in
  (alt_ergo, driver)

(* let get_fol_theory =  Pmodule.read_module "" *)

let get_loc loc =
  match loc with
  | None -> Why3.Mlw_printer.next_pos ()
  | Some l -> Loc.extract l

let why3_and l r = Ptree.Tbinnop (l, Dterm.DTand, r) |> Ptree_helpers.term
let why3_or l r = Ptree.Tbinnop (l, Dterm.DTor, r) |> Ptree_helpers.term
let unit_val = Why3.Ptree.Etuple []
