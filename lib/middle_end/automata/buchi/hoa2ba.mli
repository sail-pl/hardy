open HardyFrontEnd.Syntax
open FrontParser.SharedSyntax
open MiddleParser.HoaSyntax


module Make : (Atom : Atom.S with  type 'a t = 'a)  (_ : BoolA with type 'a t = Atom.atom) ->
    BuchiSig.S with 
    type init_val = hoa and  
    type E.label = string bool_a and
    type vdata = (name: string * acceptant: bool * start:bool)

    


module SpinHoaOutput : AutSig.ToolSig with 
        type input = string HardyFrontEnd.Syntax.Ltl.ltl and
        type output = hoa

module PpLTLHoaOutput : AutSig.ToolSig with 
        type input = string Ppltl.pltl HardyFrontEnd.Syntax.Ltl.ltl and
        type output = hoa
