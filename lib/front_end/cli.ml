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



type config = {
  ltl_atom: ltl_atom_t;
  aut_format: aut_format_t;
  file : string;
  verbose : bool;
  outdir : string;
  no_i_a_conj : bool;
  smoke_tests : bool; 
  dump_automata : bool;
}

module type CliSig =  sig
  val get_config : config
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
    let dump_automata = ref false

    let speclist =
      [
        ("-s", Set_string ltl_atom, "What is inside an LTL specification : direct (default) or ppltl for pure past ltl");
        ("-a", Set_string aut_format, "Automaton format: hoa (uses spot's ltl2tgba, default) or neverclaim (uses ltl2ba) ");
        ("-da", Set dump_automata, "Dump specification automata used to generate triples, including their dot representation");
        ("-v", Set verbose, "Debug output");
        ( "-noiaconj",
          Set no_i_a_conj,
          "Do not add the rely the formula to the guarantee one" );

        ("-smoketests", Set smoke_tests,
        "Replace all ensures with false to detect inconsistent specification")
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

    let get_config : config =
      try {
        ltl_atom = ltl_atom_t_of_string !ltl_atom;
        aut_format = aut_format_t_of_string !aut_format;
        file = !input_file;
        verbose = !verbose;
        outdir = output_path;
        no_i_a_conj = !no_i_a_conj;
        smoke_tests = !smoke_tests;
        dump_automata = !dump_automata;
      } with
      | IncorrectAtom -> failwith @@ Format.sprintf "incorrect atom '%s'" !ltl_atom
      | IncorrectAutFormat -> failwith @@ Format.sprintf "incorrect automaton format '%s'" !aut_format
  end
