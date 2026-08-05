open FrontParser
open HardyFrontEnd
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
  (Program : SIMP_TYPE)
  (AtomStore : Atom.S  with type 'a t := 'a  (* effectful version for simplicity *) )
  (TempSpec : BoolA)
  (Tool : AutSig.ToolSig with type input = string TempSpec.t) (* *)
  (B: BuchiSig.S 
            with type init_val = Tool.output
            and type E.label = string bool_a
            and type vdata = (name: string * acceptant: bool * start:bool)
  )
  (BProd : BuchiSig.S with type init_val = B.t * B.t
  )
        
   : GenSig.S 
   with   
    type temp_spec = (AtomStore.atom TempSpec.t, FrontSig.temp_f_prop) labeled and
    type in_pgrm = Program.t and
    type spec_data = unit and
    type automaton = BProd.t
  = 

struct
  type tool_input = (string * Tool.input) hoare_pair
  type tool_output = (string * Tool.output) hoare_pair

  type temp_spec = (AtomStore.atom TempSpec.t, FrontSig.temp_f_prop) labeled
  type local_spec = LocalSpec.t

  type spec_data = unit

  type in_pgrm = Program.t
  
  type in_t = (temp_spec, spec_data,in_pgrm) prog_with_spec
  type out_t = (temp_spec, spec_data, in_pgrm) prog_with_spec

  type automaton = BProd.t

  let proposify = TempSpec.map AtomStore.(register_atom >> map snd)

  let spec_to_input (cli : Cli.config) (spec : (AtomStore.atom TempSpec.t, 'a) labeled list hoare_pair) : tool_input =
    let print_formula (name, spec : string * _ ) =
      if cli.verbose then
        Format.(printf "%s formula: %a@." name (TempSpec.pp (fun fmt -> AtomStore.(get_atom_ids >> map snd >> (map (pp_print_string fmt))))) spec)
    in

    (* flatten the conjunction of formulas to a single formula *)
    let fjoin : (AtomStore.atom TempSpec.t, 'a) labeled list -> AtomStore.atom TempSpec.t = fold_mjoin (fun x -> x.value) TempSpec.conj TempSpec.tt in
    let rely = ("rely", fjoin spec.pre) in
    let rely_spec = pair_map (Right proposify) rely in
    let guarantee = ("guarantee", fjoin spec.post) in
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
    { pre = rely_spec; post = guarantee_spec}

  let output_file (cli : Cli.config) name ext =
    Filename.(concat cli.outdir (name ^ ext))

  let exec (cli : Cli.config) (i : tool_input) : tool_output =
    let call_tool ((name, spec) : string * Tool.input) :
        string * Tool.output =
      let file = output_file cli name in
      (name, Tool.call cli file spec)
    in
    (* transform each LTL formula to a buchi automaton  *)
    { pre = call_tool i.pre; post = call_tool i.post}

  let automaton_to_dot (type t) (module G : BuchiSig.S with type t = t) cli
      ((name, auto) : string * G.t) =
    let module D = BuchiSig.Dot (G) in
    (* output a dot file of the automaton *)
    Out_channel.with_open_text (output_file cli name ".dot") (fun o ->
        D.output_graph o auto)

  (* let check_safety (name,g) =
    let module U = BuchiSig.Utils(B) in   
    match U.get_nonacc_states g with
    | [] -> ()
    | l -> failwith Format.(asprintf "unsafe automaton caused by cycles %a" 
      (pp_print_list 
        ~pp_sep:(fun fmt () -> pp_print_string fmt " ") 
        (fun fmt -> fprintf fmt "[%a]" 
          (pp_print_list 
            ~pp_sep:(fun fmt () -> pp_print_string fmt "-") 
            (fun fmt v -> let (~name,..) = B.get_vdata v in pp_print_string fmt name)
          )
        )
      ) 
      l
    ) *)



  let output_to_automaton (cli : Cli.config) (o : tool_output) : automaton =
    let rely_a = 
      if cli.verbose then
        Format.printf "Creating assumptions automaton...@.";
      pair_map (Right B.create) o.pre
    in
    if cli.dump_automata then 
      automaton_to_dot (module B) cli rely_a;
    (* check_safety rely_a; *)

    let guarantee_a = 
      if cli.verbose then
        Format.printf "Creating guarantees automaton...@.";
      pair_map (Right B.create) o.post 
    in
    if cli.dump_automata then 
      automaton_to_dot (module B) cli guarantee_a;
    (* check_safety guarantee_a; *)
  
    if cli.verbose then
      Format.printf "Creating synchronized product...@."
    ;
    let prod_a =
      ("product", BProd.create (snd rely_a, snd guarantee_a))
    in
    if cli.dump_automata then 
    begin
    automaton_to_dot (module BProd) cli prod_a;
    end;
    snd prod_a
end