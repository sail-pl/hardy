open HardyFrontEnd
open FrontSig
open Syntax
open HardyMiddleEnd
open Interactive
open Automata
open Buchi
open HardyMisc.Utils
open Obby.Ltl


(* atoms are FOL formulas *)
module AtomicFormula = struct 
  type t = ((Instant.instant option * Shared.ty, Shared.base_ty) Spec.fol_t, temp_f_prop) labeled

    
  let pp_atom : Format.formatter -> _ -> unit =  fun fmt a ->
      Printer.( pp_fol 
          (pp_pred @@ pp_exp (fun fmt e -> failwith "todo") (fun fmt (s,(t,_)) -> pp_hist fmt (s,t))) 
          (Format.pp_print_option pp_base_ty)) fmt a

  let pp : Format.formatter -> t -> unit = fun fmt a -> pp_atom fmt a.value

end 


module Atom = Atom.Imperative(struct type t = Instant.min_nb_instants end)(AtomicFormula)

(* Labeling of automaton edges *)
module Label : FrontParser.SharedSyntax.BoolA with type 'a t = AtomicFormula.t
= struct
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

  let atomic (a : ((Instant.instant option * Shared.ty, Shared.base_ty) Spec.fol_t, temp_f_prop) labeled) : Atom.atom = a

end

(* High-level program specification *)
module LTLSpec : FrontParser.SharedSyntax.BoolA 
  with type 'a t = 'a Ltl.ltl
= struct
  open FrontParser.Specification.LTLSyntax

  type 'a t = 'a ltl
  type atom = {t : 'a. 'a}
  let conj = and_ltl
  let disj = disj_ltl
  let map m = map_ltl_pred m
  let pp f = Printer.(pp_ltl_default f)
  let tt = true_ltl
  let ff = false_ltl
  let atomic a = atom_ltl a.t
  let neg = not_ltl
  
end


module Parsing : Parsing.S with type out_t = (Spec.parsed_temp_spec_t, Spec.parsed_spec_t) Obby.Syntax.program
= struct 
  type temp_spec = Spec.parsed_temp_spec_t
  type local_spec = Spec.parsed_spec_t
  type in_t = unit
  type out_t = (temp_spec, local_spec) Obby.Syntax.program
  include FrontParser.ObbyLtlParser
end


open Hoa2ba 
(*
  todo: change automata type using aut_format 
*)

module Typing = Typing.M
module B = Make(Atom)(Label)
module BProd = BaProduct.Make(B)

module Middle = Generation.M(struct type t = Spec.base_spec_t end)(struct type t = (Spec.base_spec_t, Shared.ty, Shared.ty Loopy.Syntax.env) Loopy.Syntax.program end)(Atom)(LTLSpec)(SpinHoaOutput)(B)(BProd)

module Triples(Cli : Cli.CliSig) : Automata.GenSig.TriplesSig = struct
  type in_t = unit
  type out_t = unit
  type automaton = unit
  let generate_triples = fun () () -> ()
end

module Interactive(Cli: Cli.CliSig) = Why3Prover.M(struct type t =  Middle.in_t  end)(struct include Triples(Cli) type t = out_t end)

module Back(Cli: Cli.CliSig) = struct
  
end
