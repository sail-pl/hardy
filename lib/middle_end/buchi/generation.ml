open FrontParser
open HardyFrontEnd
open MiddleParser
module PSyn = HardyFrontEnd.Syntax
open ProgramSyntax
open HardyMisc.Utils
open LTLSyntax
module SSyn = Syntax.Shared
module Hist = Syntax.Instant

(** {1 Build Buchi Automaton from string formula} *)

module InputSpec = struct
  open Printer

  type t = string ltl

  let string_of_ltl_full =
    string_of_ltl
      (fun p -> Triples.Atom.add_and_get p |> snd)
      string_of_ltl_binop string_of_ltl_unop

  let string_of_ltl_short =
    string_of_ltl
      (fun p -> Triples.Atom.add_and_get p |> fst)
      string_of_ltl_binop string_of_ltl_unop

  let from_ltl : _ ltl -> t =
    map_ltl_pred (fun p -> Triples.Atom.add_and_get p |> snd)
end

module M :
  Sig.S
    with type triple_data = Program.triple_data_t
     and type fol_data = Hist.min_nb_instants = struct
  type input = (string * string ltl) hoare_pair
  type fol_data = Hist.min_nb_instants
  type triple_data = Program.triple_data_t
  type in_program = PSyn.base_program

  (* (SSyn.ty PSyn.temp_spec_t, (SSyn.ty,unit) PSyn.inst_spec_t, PSyn.variant_t, unit) program *)
  type triples =
    ( triple_data,
      (SSyn.ty, fol_data) PSyn.inst_spec_t disjunction conjunction )
    hoare_triple
    list

  type output = input * (string * NcSyntax.neverclaim) hoare_pair
  type automaton = Triples.BProd.t
  (* { pa_pair :  (string * B.t) P.hoare_pair; pa_prod : (string * BB.t) } *)

  let spec_to_input (cli : Cli.info)
      (spec : SSyn.ty PSyn.temp_spec_t list hoare_pair) : input =
    let print_formula (name, spec) =
      if cli.verbose then
        Format.printf "%s formula : @,%s@," name
          (InputSpec.string_of_ltl_short spec)
    in

    let fjoin = fold_mjoin Fun.id and_ltl true_ltl in
    let rely = ("rely", fjoin spec.requires) in
    print_formula rely;
    let rely_spec = pair_map (Right InputSpec.from_ltl) rely in
    let guarantee = ("guarantee", fjoin spec.ensures) in
    print_formula guarantee;

    let guarantee_spec =
      pair_map
        (Right
           (fun g ->
             (* because the input is read-only, any predicate on input is
          obviously still true at the end of the instant.
          It is added to the guarantee formula to potentialy simplify
          the product automaton.
      *)
             (if cli.no_i_a_conj || snd rely = true_ltl then g
              else and_ltl (snd rely) g)
             |> InputSpec.from_ltl))
        guarantee
    in
    { requires = rely_spec; ensures = guarantee_spec }

  let output_file (cli : Cli.info) name ext =
    Filename.(concat cli.outdir (name ^ ext))

  let exec (cli : Cli.info) (i : input) : output =
    let ltl2ba_nc ((name, spec) : string * InputSpec.t) :
        string * NcSyntax.neverclaim =
      let never_file = output_file cli name ".never" in
      (name, Ltl2nc.ltl_to_neverclaim cli never_file spec)
    in
    (* transform LTL formula to a neverclaim representation of a buchi automaton  *)
    i,{ requires = ltl2ba_nc i.requires; ensures = ltl2ba_nc i.ensures }

  let automaton_to_dot (type t) (module G : BuchiSig.S with type t = t) cli
      ((name, auto) : string * G.t) =
    let module D = BuchiSig.Dot (G) in
    (* output a dot file of the automaton *)
    Out_channel.with_open_text (output_file cli name ".dot") (fun o ->
        D.output_graph o auto)

  let output_to_automaton (cli : Cli.info) (i,o : output) : automaton =
    let rely_a = pair_map (Right Triples.B.create) o.requires
    and guarantee_a = pair_map (Right Triples.B.create) o.ensures in
    automaton_to_dot (module Triples.B) cli rely_a;
    automaton_to_dot (module Triples.B) cli guarantee_a;
    (* check automata exactly represents the formulas *)
    let module V = Validator.Verif.M (Triples.B) (Triples.Atom)  in
    V.verif_a ((snd i.requires,snd rely_a), (snd i.ensures, snd guarantee_a));

    (* create synchronized product automaton *)
    let prod_a =
      ("product", Triples.BProd.create (snd rely_a, snd guarantee_a))
    in
    automaton_to_dot (module Triples.BProd) cli prod_a;
    snd prod_a

  let generate_triples : in_program -> automaton -> triples =
    Triples.generate_triples
end
