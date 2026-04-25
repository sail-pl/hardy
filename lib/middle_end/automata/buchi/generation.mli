open FrontParser
open HardyFrontEnd
open HardyMisc.Utils
open SharedSyntax

(** 
Temporal formulas are converted to automatas after proposification of their atoms and combined using automata product

- [TempSpec] is the temporal specification
- AtomStore is in charge of the proposification, [AtomStore.atom] 
 *)
module M :
(LocalSpec : HardyMisc.Utils.SIMP_TYPE)
(AtomStore : Atom.S  with type 'a t := 'a)
(TempSpec : SharedSyntax.BoolA)
(Tool : AutSig.ToolSig with type input = string TempSpec.t)
(B : BuchiSig.S 
            with type init_val = Tool.output
            and type E.label = string bool_a)
(BProd : BuchiSig.S with type init_val = B.t * B.t) -> GenSig.S with   
    type local_spec = LocalSpec.t and 
    type temp_spec = (AtomStore.atom TempSpec.t, FrontSig.temp_f_prop) labeled and
    type automaton = BProd.t
