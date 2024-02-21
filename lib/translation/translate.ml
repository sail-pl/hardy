module T = TranslateUtils

type info = T.info

module type TranslateSIG = sig
  val translate_program :
    info -> ArduinoSyntax.Syntax.program -> TranslateUtils.P.mlw_file
end

(* entry point to the different translations *)
module LTL : TranslateSIG = TranslateLTL
module FOL : TranslateSIG = TranslateFOL

