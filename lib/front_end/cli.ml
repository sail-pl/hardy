(** {1 Command Line Interface}*)

type info = {
  file : string;
  ltl2baPath : string;
  verbose : bool;
  outdir : string;
  no_i_a_conj : bool;
  eval: bool;
}
(** parameters provided by the cli *)

(** Applicative functor because of side-effects inside *)
module type CliSig = functor () -> sig
  val get_info : info
end

module Init : CliSig =
functor
  ()
  ->
  struct
    open Arg

    let usage_msg =
      Format.sprintf "Usage : %s --ltl2ba <ltl2ba exe> <file> [-v]"
        (Sys.argv.(0) |> Filename.basename)

    let input_file = ref ""
    let verbose = ref false
    let no_i_a_conj = ref false
    let ltl2baPath = ref ""
    let cwd = Sys.getcwd ()

    let eval = ref false

    let parseLtl2baPath p =
      if not @@ Sys.file_exists p then raise @@ Bad "Can't stat ltl2ba program"
      else ltl2baPath := p

    let speclist =
      [
        ("-v", Set verbose, "debug output");
        ( "-noiaconj",
          Set no_i_a_conj,
          "do not add the rely the formula to the guarantee one" );
        ("-ltl2ba", String parseLtl2baPath, "set ltl2ba program path");
        ("-run", Set eval, "evaluate the program");
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

    let get_info : info =
      {
        file = !input_file;
        ltl2baPath = !ltl2baPath;
        verbose = !verbose;
        outdir = output_path;
        no_i_a_conj = !no_i_a_conj;
        eval = !eval
      }
  end
