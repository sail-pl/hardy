module Cli = HardyFrontEnd.Cli

module type ToolSig = sig
  type input
  type output

  val call : Cli.info -> (string -> string) ->  input -> output
  
end