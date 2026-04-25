open FrontParser.SharedSyntax
open MiddleParser.NcSyntax

module Make :
(Atom : Atom.S with  type 'a t = 'a) (_ : BoolA with type 'a t = Atom.atom) -> 
    BuchiSig.S with  type init_val = neverclaim

module Ltl2baNcOutput : AutSig.ToolSig with 
        type input = string HardyFrontEnd.Syntax.Ltl.ltl and
        type output = neverclaim

module SpinNcOutput : AutSig.ToolSig with 
    type input = string HardyFrontEnd.Syntax.Ltl.ltl and
    type output = neverclaim
