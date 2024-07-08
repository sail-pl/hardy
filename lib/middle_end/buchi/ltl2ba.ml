open HardyFrontEnd
open Syntax
open Ltl
open MiddleParser

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

let ltl_to_neverclaim (i : Cli.info) (never_file : string) (f : string ltl) :
    NcSyntax.neverclaim =
  let to_spin = Printer.string_of_ltl Fun.id spin_binop spin_unop in
  let cmd =
    Filename.quote_command i.ltl2baPath
      [ "-f"; to_spin f ]
      ~stdout:never_file ~stderr:(never_file ^ ".err")
  in
  if i.verbose then Format.printf "ltl2ba command line : %s" cmd;
  let ret = Sys.command cmd in
  if ret <> 0 then
    failwith Format.(sprintf "non-0 exit-code (%i) from ltl2ba" ret)
  else NcParsing.parse_automaton never_file
