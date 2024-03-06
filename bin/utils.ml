open Why3

type w3 = { config : Whyconf.config; main : Whyconf.main; env : Env.env }

module T = ArduinoTranslation.Ltl2ba

let init_why3 () : w3 =
  let open Whyconf in
  let config = init_config None in
  let main = get_main config in
  let env = loadpath main |> Env.create_env in
  { config; main; env }

let print_program p =
  p |> Fun.flip (Mlw_printer.pp_mlw_file ~attr:true) |> Pp.print_in_file

module type CliSig = functor () -> sig
  val get_info : T.info
end

module Cli : CliSig =
functor
  ()
  ->
  struct
    open Arg

    let usage_msg =
      Printf.sprintf "Usage : %s --ltl2ba <ltl2ba exe> <file> [-v] [-pltl]"
        (Sys.argv.(0) |> Filename.basename)

    let input_file = ref ""
    let pltl_mode = ref false
    let verbose = ref false
    let ltl2baPath = ref ""
    let cwd = Sys.getcwd ()

    let parseLtl2baPath p =
      if not @@ Sys.file_exists p then raise @@ Bad "Can't stat ltl2ba program"
      else ltl2baPath := p

    let speclist =
      [
        ("-v", Set verbose, "debug output");
        ("-ltl2ba", String parseLtl2baPath, "set ltl2ba program path");
      ]

    let get_input_file f =
      if not @@ Sys.file_exists f then
        raise @@ Bad (Format.sprintf "Can't stat file '%s'" f)
      else if !input_file = "" then input_file := f
      else raise @@ Bad "exactly one file expected"

    let () = Arg.parse speclist get_input_file usage_msg
    let () = if !input_file = "" then failwith "one input file needed"
    let () = if !ltl2baPath = "" then failwith "ltl2ba path needed"
    let dir = Filename.(!input_file |> remove_extension |> basename) ^ "_gen"

    (* drop generated files in $cwd/<filename>_gen/ *)
    let output_path = Filename.(concat cwd dir)

    let get_info : T.info =
      {
        file = !input_file;
        ltl2baPath = !ltl2baPath;
        pltl_mode = !pltl_mode;
        verbose = !verbose;
        outdir = output_path;
      }
  end

(* let get_fol_theory =  Pmodule.read_module "" *)
