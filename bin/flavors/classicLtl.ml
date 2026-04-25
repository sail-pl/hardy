open HardyFrontEnd
open Syntax
open HardyMiddleEnd
open Automata
open Buchi
open Hoa2ba
open HardyMisc.Utils
open Program
open FrontSig
open Ltl_spec


(* atoms are FOL formulas *)
module AtomicFormula = struct 
  type t = ((Instant.instant option * Shared.ty, Shared.base_ty) fol_t, temp_f_prop) labeled

    
  let pp_atom : Format.formatter -> _ -> unit =  fun fmt a ->
      Printer.( pp_fol 
          (pp_pred @@ pp_exp (fun fmt (s,(t,_)) -> pp_hist fmt (s,t))) 
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

  let atomic (a : ((Instant.instant option * Shared.ty, Shared.base_ty) fol_t, temp_f_prop) labeled) : Atom.atom = a

end

(* High-level program specification *)
module LTLSpec : FrontParser.SharedSyntax.BoolA 
  with type 'a t = 'a Ltl.ltl
= struct
  open LTLSyntax

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


module Parsing : Parsing.S with 
  type local_spec = parsed_spec_t and
  type temp_spec = parsed_temp_spec_t

= struct 
  type temp_spec = parsed_temp_spec_t
  type local_spec = parsed_spec_t

  type t = (temp_spec, unit, local_spec, unit, ProgramSyntax.parsed_env) program
  include FrontParser.PgrmLtlParser
end



module Typing = HardyFrontEnd.Ltl_typing.M
module B = Make(Atom)(Label)
module BProd = BaProduct.Make(B)

module Middle = Generation.M(struct type t = Typing.out_local_spec end)(Atom)(LTLSpec)(SpinHoaOutput)(B)(BProd)

module Triples = Triples_ltl.M(Ltl_spec)(Atom)(B)(BProd)

module Interactive(Cli: Cli.CliSig) = Why3Prover.M(struct type t = base_spec_t end)(struct type t = Typing.out_temp_spec end)(Triples(Cli))

module Back = HardyBackEnd.Why3_back.Ltl.M(Ltl_spec)
