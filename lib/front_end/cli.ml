(** {1 Command Line Interface}*)

type ltl_atom_t = Direct | PastLTL

exception IncorrectAtom
let ltl_atom_t_of_string = function
  | "Direct" | "direct" | "" (*default*) -> Direct
  | "Pure-PastLtl" | "pure-pastltl" | "ppltl" -> PastLTL
  | _ -> raise IncorrectAtom

let string_of_ltl_atom_t = function Direct -> "Direct" | PastLTL -> "Past LTL"

type aut_format_t = Neverclaim | HOA 

exception IncorrectAutFormat

let aut_format_t_of_string = function
  | "HOA" | "hoa" | "" (*default*) -> HOA
  | "NC" | "nc" | "neverclaim" -> Neverclaim
  | _ -> raise IncorrectAutFormat

let string_of_aut_format_t = function HOA -> "HOA format" | Neverclaim -> "Neverclaim"



type info = {
  ltl_atom: ltl_atom_t;
  aut_format: aut_format_t;
  file : string;
  verbose : bool;
  outdir : string;
  no_i_a_conj : bool;
  smoke_tests : bool; 
}
(** parameters provided by the cli *)

(** Applicative functor because of side-effects inside *)
module type CliSig =  sig
  val get_info : info
end

module Init : functor () -> CliSig =
functor
  ()
  ->
  struct
    open Arg

    let usage_msg =
      Format.sprintf "Usage : %s <file> [-v]"
        (Sys.argv.(0) |> Filename.basename)

    let input_file = ref ""
    let verbose = ref false
    let no_i_a_conj = ref false
    let smoke_tests = ref false
    let cwd = Sys.getcwd ()
    let ltl_atom = ref ""
    let aut_format = ref ""

    let speclist =
      [
        ("-s", Set_string ltl_atom, "what is inside an LTL specification : direct (default) or ppltl for pure past ltl");
        ("-a", Set_string aut_format, "automaton format: hoa (uses spot's ltl2tgba, default) or neverclaim (uses ltl2ba) ");
        ("-v", Set verbose, "debug output");
        ( "-noiaconj",
          Set no_i_a_conj,
          "do not add the rely the formula to the guarantee one" );

        ("-smoketests", Set smoke_tests,
        "replace all ensures with false to detect inconsistent specification")
      ]

    let get_input_file f =
      if not @@ Sys.file_exists f then
        raise @@ Bad (Format.sprintf "Can't stat file '%s'" f)
      else if !input_file = "" then input_file := f
      else raise @@ Bad "exactly one file expected"

    let () = Arg.parse speclist get_input_file usage_msg
    let () = if !input_file = "" then failwith "one input file needed"
    let dir = Filename.(!input_file |> remove_extension |> basename) ^ "_gen"

    (* drop generated files in $cwd/<filename>_gen/ *)
    let output_path = Filename.(concat cwd dir)

    let get_info : info =
      try {
        ltl_atom = ltl_atom_t_of_string !ltl_atom;
        aut_format = aut_format_t_of_string !aut_format;
        file = !input_file;
        verbose = !verbose;
        outdir = output_path;
        no_i_a_conj = !no_i_a_conj;
        smoke_tests = !smoke_tests;
      } with
      | IncorrectAtom -> failwith @@ Format.sprintf "incorrect atom '%s'" !ltl_atom
      | IncorrectAutFormat -> failwith @@ Format.sprintf "incorrect automaton format '%s'" !aut_format
  end
