open FrontParser
open ProgramSyntax
open HardyFrontEnd
(* open MiddleParser *)
open HardyMisc.Utils
open SharedSyntax
module SSyn = Syntax.Shared
module Hist = Syntax.Instant

(** 
  Temporal formulas are converted to automatas after proposification of their atoms and combined using automata product
 
  - [TempSpec] is the temporal specification
  - AtomStore is in charge of the proposification, [AtomStore.atom] 
 
 
  *)
module M
  (LocalSpec : SIMP_TYPE)
  (AtomStore : Atom.S  with type 'a t := 'a  (* effectful version for simplicity *) )
  (TempSpec : BoolA)
  (Tool : AutSig.ToolSig with type input = string TempSpec.t) (* *)
  (B: BuchiSig.S 
            with type init_val = Tool.output
            and type E.label = string bool_a
  )
  (BProd : BuchiSig.S with type init_val = B.t * B.t
  )
        
   : GenSig.S 
   with   
  
  type local_spec = LocalSpec.t and 
  type temp_spec = (AtomStore.atom TempSpec.t, FrontSig.temp_f_prop) labeled and

  type automaton = BProd.t
  = 

struct
  type tool_input = (string * Tool.input) hoare_pair
  type tool_output = (string * Tool.output) hoare_pair

  type temp_spec = (AtomStore.atom TempSpec.t, FrontSig.temp_f_prop) labeled
  type local_spec = LocalSpec.t

  type in_program = (temp_spec,unit, local_spec, ty, ty env) program

  type automaton = BProd.t

  let proposify = TempSpec.map AtomStore.(register_atom >> map snd)

  let spec_to_input (cli : Cli.info) (spec : (AtomStore.atom TempSpec.t, 'a) labeled list hoare_pair) : tool_input =
    let print_formula (name, spec : string * _ ) =
      if cli.verbose then
        Format.(printf "%s formula: %a@." name (TempSpec.pp (fun fmt -> AtomStore.(get_atom_ids >> map snd >> (map (pp_print_string fmt))) >> ignore)) spec)
    in

    (* flatten the conjunction of formulas to a single formula *)
    let fjoin : (AtomStore.atom TempSpec.t, 'a) labeled list -> AtomStore.atom TempSpec.t = fold_mjoin (fun x -> x.value) TempSpec.conj TempSpec.tt in
    let rely = ("rely", fjoin spec.requires) in
    let rely_spec = pair_map (Right proposify) rely in
    let guarantee = ("guarantee", fjoin spec.ensures) in
    let guarantee_spec =
      pair_map
        (Right
           (fun g ->
             (* because the input is read-only and history is not updated until next instant, any predicate from the requires formula
            must still hold at the end of the instant.
          It is added to the guarantee formula to potentialy simplify
          the product automaton.
      *)
             (if cli.no_i_a_conj || snd rely = TempSpec.tt then g
              else TempSpec.conj (snd rely) g)
             |> proposify))
        guarantee
    in
    print_formula rely;
    print_formula guarantee;
    { requires = rely_spec; ensures = guarantee_spec}

  let output_file (cli : Cli.info) name ext =
    Filename.(concat cli.outdir (name ^ ext))

  let exec (cli : Cli.info) (i : tool_input) : tool_output =
    let call_tool ((name, spec) : string * Tool.input) :
        string * Tool.output =
      let file = output_file cli name in
      (name, Tool.call cli file spec)
    in
    (* transform each LTL formula to a buchi automaton  *)
    { requires = call_tool i.requires; ensures = call_tool i.ensures}

  let automaton_to_dot (type t) (module G : BuchiSig.S with type t = t) cli
      ((name, auto) : string * G.t) =
    let module D = BuchiSig.Dot (G) in
    (* output a dot file of the automaton *)
    Out_channel.with_open_text (output_file cli name ".dot") (fun o ->
        D.output_graph o auto)

  let output_to_automaton (cli : Cli.info) (o : tool_output) : automaton =
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
end