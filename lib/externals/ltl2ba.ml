open HardySyntax.PromelaSyntax
open BaParser.Parsing
open HardySyntax
open Syntax
open Fol
open Ltl

(* Move to external tools *)
(* put info as global variable *)

type info = {
  file : string;
  ltl2baPath : string;
  verbose : bool;
  pltl_mode : bool;
  outdir : string;
  no_i_a_conj : bool;
}

let spin_binop : ltl_binary -> string = function
  | Until -> "U"
  | Release -> "V"
  | LTL_BArithm Arrow -> "->"
  | LTL_BArithm Or -> "||"
  | LTL_BArithm And -> "&&"
  | LTL_BArithm Equiv -> "<->"
  | _ -> failwith "unsupported bop"

let spin_unop : ltl_unary -> string = function
  | Next -> "X"
  | Always -> "[]"
  | Eventually -> "<>"
  | LTL_UArithm Not -> "!"
  | WeakNext -> failwith "unsupported unop"

let generate_claim (i : info) (never_file : string) (f : expr fol ltl)
    (module A : AtomSig) : unit =
  let to_spin =
    Printer.string_of_ltl (fun p -> A.add_or_get p |> snd) spin_binop spin_unop
  in
  let cmd =
    Filename.quote_command i.ltl2baPath
      [ "-f"; to_spin f ]
      ~stdout:never_file ~stderr:(never_file ^ ".err")
  in
  if i.verbose then Format.printf "ltl2ba command line : %s" cmd;
  let ret = Sys.command cmd in
  if ret <> 0 then
    failwith Format.(sprintf "non-0 exit-code (%i) from ltl2ba" ret)

let read_claim (never_file : string) : neverclaim = parse_automaton never_file
