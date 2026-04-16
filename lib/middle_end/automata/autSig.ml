module Cli = HardyFrontEnd.Cli
(* open FrontParser.Program *)


(* Tool for generating the automata *)
module type ToolSig = sig
  type input
  type output

  val call : Cli.info -> (string -> string) ->  input -> output
  
end