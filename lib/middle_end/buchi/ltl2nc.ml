open HardyFrontEnd
open Syntax
open Ltl
open MiddleParser

let spin_binop : ltl_binary -> string = function
  | Until -> "U"
  | Release -> "V"
  | LTL_StdBinary Arrow -> "->"
  | LTL_StdBinary LOr -> "||"
  | LTL_StdBinary LAnd -> "&&"
  | LTL_StdBinary Equiv -> "<->"
  | _ -> failwith "unsupported bop"

let spin_unop : ltl_unary -> string = function
  | Next -> "X"
  | Always -> "[]"
  | Eventually -> "<>"
  | LTL_StdUnary LNot -> "!"

let ltl_to_neverclaim (i : Cli.info) (never_file : string) (f : string ltl) :
    NcSyntax.neverclaim =
  let to_spin = Printer.string_of_ltl Fun.id spin_binop spin_unop in
  let cmd =
    Filename.quote_command i.ltl2baPath
      [ "-f"; to_spin f ]
      ~stdout:never_file ~stderr:(never_file ^ ".err")
  in
  if i.verbose then Format.printf "ltl2ba command line : %s" cmd;

  (* do not generate neverclaim, for testing validator *)
  (* let cmd = ":" in  *)
  let ret = Sys.command cmd in
  if ret <> 0 then
    failwith Format.(sprintf "non-0 exit-code (%i) from ltl2ba" ret)
  else NcParsing.parse_automaton never_file
