module Cli = HardyFrontEnd.Cli

(** Tool for generating the automata *)
module type ToolSig =
sig
    type input
    type output
    val call : Cli.config -> (string -> string) -> input -> output
end
