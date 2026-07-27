open HardyFrontEnd
open Syntax
open HardyMiddleEnd
open Automata
open Buchi
open Hoa2ba
open Interactive
open HardyMisc.Utils
open Ppltl_spec


module AtomicFormula = struct 
  type t = ((Instant.instant option * Shared.ty, Shared.base_ty) fol_t, FrontSig.temp_f_prop) labeled

  let pp : Format.formatter -> t -> unit = fun fmt f -> 
    Printer.(pp_fol (pp_pred (pp_exp (fun fmt (s,_) -> Format.pp_print_string fmt s))) (Format.pp_print_option pp_base_ty)) fmt f.value

end 


module Atom = Atom.Imperative(struct type t = Instant.min_nb_instants end)(AtomicFormula)

(* Labeling of automaton edges *)
module Label : FrontParser.SharedSyntax.BoolA with type 'a t = AtomicFormula.t
= struct
  open FrontSig
  open Fol
  
  let label = mk_labeled ~label:dft_temp_f_prop 

  type 'a t = AtomicFormula.t

  type atom = Atom.atom

  let conj f1 f2 = mk_labeled ~label:(join_temp_f_prop f1.label f2.label) (and_fol f1.value f2.value)
  let disj f1 f2 = mk_labeled ~label:(join_temp_f_prop f1.label f2.label) (or_fol f1.value f2.value)

  let map : ('a -> 'b) -> atom -> atom = fun _ -> Fun.id

  let tt = label true_fol

  let ff = label false_fol

  let neg x = mk_labeled ~label:x.label (not_fol x.value)

  let pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> atom -> unit = fun _ -> AtomicFormula.pp

  let atomic (a : ((Instant.instant option * Shared.ty, Shared.base_ty) fol_t, temp_f_prop) labeled) : Atom.atom = a

end

module PpLTLSpec : FrontParser.SharedSyntax.BoolA 
  with type 'a t = 'a Ppltl.pltl Ltl.ltl
= struct
  open Ltl
  open PpLTLSyntax

  type 'a t = 'a Ppltl.pltl ltl
  type atom = {t : 'a. 'a}
  let conj = and_ltl
  let disj = disj_ltl
  let map m = map_ltl_pred (map_pltl_pred m)
  let pp f = Printer.(pp_ltl_default (fun fmt f' -> Format.fprintf fmt "{%a}" (pp_pltl_default f) f'))
  let tt = true_ltl
  let ff = false_ltl
  let atomic a = atom_ltl (atom_pltl a.t)
  let neg = not_ltl
  
end


module Parsing : Parsing.S with type out_t = ( Ppltl_spec.parsed_temp_spec_t, unit, (Ppltl_spec.parsed_spec_t, unit, FrontParser.LoopySyntax.parsed_env) FrontParser.LoopySyntax.program) Shared.prog_with_spec


= struct 
  type temp_spec = parsed_temp_spec_t
  type local_spec = parsed_spec_t
  
  type in_t = unit

  type out_t = (temp_spec, unit, (local_spec, unit, LoopySyntax.parsed_env) LoopySyntax.program) Shared.prog_with_spec 
  include FrontParser.LoopyPltlParser
end


module Typing = Pltl_typing.M
module B = Make(Atom)(Label)
module BProd = BaProduct.Make(B)

module Middle = Generation.M(struct type t = base_spec_t end)(struct type t = (base_spec_t, Shared.ty, Shared.ty LoopySyntax.env) LoopySyntax.program end)(Atom)(PpLTLSpec)(PpLTLHoaOutput)(B)(BProd)

module Triples = Triples.M(Ppltl_spec)(Atom)(B)(BProd)

module Interactive(Cli : Cli.CliSig) = Why3Prover.M(struct type t = Middle.in_t end)(struct include Triples(Cli)  type t = out_t end)

module Back = Back.M(Ppltl_spec)
