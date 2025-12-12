open FrontParser
open HardyFrontEnd
open MiddleParser
module PSyn = HardyFrontEnd.Syntax
open ProgramSyntax
open SyntaxCommon
open HardyMisc.Utils
open SharedSyntax
open LTLSyntax
module SSyn = Syntax.Shared
module Hist = Syntax.Instant

module M(TAtom: TseitinAtomSig)
         (Tool : Sig.ToolSig with type input = string ltl)
          (B: BuchiSig.S 
                    with type init_val = Tool.output
                    and type E.label = TAtom.t eba
                    and type TAtom.t = TAtom.t
                    and type 'a FAtom.t = 'a 
                    and type _ FAtom.data = Hist.min_nb_instants
                    and type FAtom.ty = Hist.instant option * SSyn.ty
                    and type FAtom.qty = base_ty
          )
        :
  Sig.S
    with type triple_data = Program.triple_data_t
     and type fol_data = Hist.min_nb_instants  = 
      struct
  type input = (string * Tool.input) hoare_pair
  type fol_data = Hist.min_nb_instants
  type triple_data = Program.triple_data_t
  type in_program = PSyn.base_program

  (* (SSyn.ty PSyn.temp_spec_t, (SSyn.ty,unit) PSyn.inst_spec_t, PSyn.variant_t, unit) program *)
  type triples =
    ( triple_data,
      (SSyn.ty,SSyn.base_ty, fol_data) PSyn.inst_spec_t Sig.formula )
    hoare_triple
    list

  module BProd = BaProduct.Make(B)
  module Triples = Triples.M(TAtom)(B)(BProd)

  type output = (string * Tool.output) hoare_pair
  type automaton = BProd.t
  (* { pa_pair :  (string * B.t) P.hoare_pair; pa_prod : (string * BB.t) } *)

  (* let pp_ltl_full =
    Printer.(pp_ltl
      (fun fmt p -> Format.pp_print_string fmt (B.FAtom.add_and_get p |> snd))
      pp_ltl_binop pp_ltl_unop) *)

  let pp_ltl_short fmt : (_ PSyn.fol_t, PSyn.temp_f_prop) labeled ltl  -> unit =
    Printer.(pp_ltl
      (fun fmt p -> Format.pp_print_string fmt (B.FAtom.add_and_get p.value |> fst))
      pp_ltl_binop pp_ltl_unop) fmt

  let from_ltl : _ ltl -> string ltl =
    map_ltl_pred (fun p -> B.FAtom.add_and_get p.value |> snd)


  let spec_to_input (cli : Cli.info)
      (spec : PSyn.base_temp_spec_t list hoare_pair) : input =
    let print_formula (name, spec : string * (_ PSyn.fol_t, PSyn.temp_f_prop) labeled ltl) =
      if cli.verbose then
        Format.printf "%s formula: %a@." name
          pp_ltl_short spec
    in

    (* flatten the conjunction of formulas to a single formula *)
    let fjoin : PSyn.base_temp_spec_t list -> _ = fold_mjoin (fun x -> x.value) and_ltl true_ltl in
    let rely = ("rely", fjoin spec.requires) in
    print_formula rely;
    let rely_spec = pair_map (Right from_ltl) rely in
    let guarantee = ("guarantee", fjoin spec.ensures) in
    print_formula guarantee;

    let guarantee_spec =
      pair_map
        (Right
           (fun g ->
             (* because the input is read-only and history is not updated until next instant, any predicate from the requires formula
            must still hold at the end of the instant.
          It is added to the guarantee formula to potentialy simplify
          the product automaton.
      *)
             (if cli.no_i_a_conj || snd rely = true_ltl then g
              else and_ltl (snd rely) g)
             |> from_ltl))
        guarantee
    in
    { requires = rely_spec; ensures = guarantee_spec }

  let output_file (cli : Cli.info) name ext =
    Filename.(concat cli.outdir (name ^ ext))

  let exec (cli : Cli.info) (i : input) : output =
    let call_tool ((name, spec) : string * Tool.input) :
        string * Tool.output =
      let file = output_file cli name in
      (name, Tool.call cli file spec)
    in
    (* transform each LTL formula to a buchi automaton  *)
    { requires = call_tool i.requires; ensures = call_tool i.ensures }

  let automaton_to_dot (type t) (module G : BuchiSig.S with type t = t) cli
      ((name, auto) : string * G.t) =
    let module D = BuchiSig.Dot (G) in
    (* output a dot file of the automaton *)
    Out_channel.with_open_text (output_file cli name ".dot") (fun o ->
        D.output_graph o auto)

  let output_to_automaton (cli : Cli.info) (o : output) : automaton =
    let rely_a = pair_map (Right B.create) o.requires
    and guarantee_a = pair_map (Right B.create) o.ensures in
    automaton_to_dot (module B) cli rely_a;
    automaton_to_dot (module B) cli guarantee_a;
    (* create synchronized product automaton *)
    let prod_a =
      ("product", BProd.create (snd rely_a, snd guarantee_a))
    in
    automaton_to_dot (module BProd) cli prod_a;
    snd prod_a

  let generate_triples : in_program -> automaton -> triples =
    Triples.generate_triples
end