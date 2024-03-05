module L = Lexing
module A = Automaton
open TranslateUtils
open ArduinoSyntax.Locations
open ArduinoSyntax.Syntax
open ArduinoSyntax.Printer
open ArduinoSyntax.Automaton
module Atoms = Atom ()
module Buchi = A.Buchi (Atoms)
module DotG = A.BuchiDot (Buchi)
module PG = A.BuchiProd (Buchi) (Atoms)
module DotPG = A.BuchiDot (PG)

let compute_automaton (f : string) (i : info) (output_file : string -> string) =
  (* ltl3ba presentation : https://pdfs.semanticscholar.org/6d7d/04f5255cccf22108468747037be889e3f535.pdf *)
  let open BaParser.Parsing in
  let never_file = output_file ".never" in

  let cmd =
    Filename.quote_command i.ltl2baPath [ "-f"; f ] ~stdout:never_file
      ~stderr:(never_file ^ ".err")
  in

  if i.verbose then Format.printf "ltl2ba command line : %s" cmd;

  let ret =
    Sys.command
    @@ Filename.quote_command i.ltl2baPath [ "-f"; f ] ~stdout:never_file
         ~stderr:(never_file ^ ".err")
  in

  if ret <> 0 then
    failwith Format.(sprintf "non-0 exit-code (%i) from ltl2ba" ret);

  let auto = parse_automaton never_file |> Buchi.create in

  Out_channel.with_open_text (output_file ".dot") (fun o ->
      DotG.output_graph o auto);
  auto

let string_of_ltl_full = string_of_ltl (fun p -> Atoms.add p |> snd)
let string_of_ltl_short = string_of_ltl (fun p -> Atoms.add p |> fst)

let ltl_conjunction f1 f2 =
  match (f1, f2) with
  | Some (LTL f1), Some (LTL f2) ->
      Some (LTL { loc = f1.loc; value = LTL_Binary (f1, LTL_BArithm And, f2) })
  | Some (LTL f), None | None, Some (LTL f) -> Some (LTL f)
  | None, None -> None
  | _ -> failwith "not a LTL formula"

let make_automaton info ((req, ens) : 'a option * 'a option) =
  let output_file name ext = Filename.(concat info.outdir (name ^ ext)) in

  let translate_spec (name : string) = function
    | LTL f ->
        let f_str = string_of_ltl_full f in
        (if info.verbose then
           let f_str_short = string_of_ltl_short f in
           Format.printf "\n %s formula : \n%s\n" name f_str_short);
        compute_automaton f_str info (output_file name)
    | _ -> failwith "not a LTL formula"
  in

  let true_if_none = Option.value ~default:(LTL (mk_dummy_loc LTL_True)) in
  let rely_a = true_if_none req |> translate_spec "rely" in
  let guarantee_a =
    true_if_none (ltl_conjunction req ens) |> translate_spec "guarantee"
  in

  let prod_a = PG.create (rely_a, guarantee_a) in
  Out_channel.with_open_text (output_file "product" ".dot") (fun o ->
      DotPG.output_graph o prod_a);
  prod_a

(* create a map binding the exit-arc rely formula to all its guarantee ones *)
module M = Map.Make (struct
  type t = AS.bform

  let compare e1 e2 =
    String.compare (e1 |> string_of_bform Fun.id) (e2 |> string_of_bform Fun.id)
end)

(* problem with invariant instead of formula *)
(* let combine (f : fol -> fol -> bol) *)

let bform_to_fol : bform -> fol = fol_of_bform (fun a -> Atoms.get a |> snd)
let combine_fol f1 op f2 = mk_dummy_loc (FOL_Binary (f1, op, f2))
let false_fol : fol = mk_dummy_loc FOL_False
let and_fol (f1 : fol) (f2 : fol) : fol = mk_dummy_loc (FOL_Binary (f1, Or, f2))
let or_fol (f1 : fol) (f2 : fol) : fol = mk_dummy_loc (FOL_Binary (f1, Or, f2))

let exists_fol (vars : (string * ty) list) (f : fol) : fol =
  mk_dummy_loc (Exists (vars, f))

(**   [make_prod_spec input in_e out_e init_post] 
      builds the list of [Ptree.spec] for a node of the product graph 
      - [input : (string * ty) list] inputs of the program  
      - [in_e : PG.edge list] entry edges 
      - [out_e : PG.edge list] exit edges 
      - [init_post] the initial formula if the node is a start node
      For each input formula occuring in exit edges, computes 
        {(g_1 \/ ... \/ g_n) /\ <init_post> /\ f} 
        { g_1' \/ ... \/ g_m'}
        where (., g_i') are in in_e and (f,g_i) are in out_e
        and init is there if defined. 
      *)
let make_prod_spec (input : (string * ty) list) (in_e : PG.E.t list)
    (out_e : PG.E.t list) (init_post : fol option) : fol list hoare_pair list =
  assert (not (List.is_empty out_e));
  assert ((not (List.is_empty in_e)) || Option.is_some init_post);
  let m =
    (* Factorize exit edges by common first component by buildin a map from
       first components to matching second components *)
    List.fold_left
      (fun m e ->
        let l = PG.E.label e in
        M.add_to_list l.requires l.ensures m)
      M.empty out_e
  in
  (* construct the spec for each first component *)
  M.fold
    (fun (k : bform) (d : bform list) s ->
      let requires =
        let exists_dij =
          (* disjonction of second components with input universally quantified *)
          List.fold_left
            (fun acc e -> or_fol (bform_to_fol (PG.E.label e).ensures) acc)
            false_fol in_e
          |> exists_fol input
        in
        let with_init =
          (* if initial node, add ensures from setup  *)
          Option.fold init_post ~none:exists_dij ~some:(fun i ->
              or_fol i exists_dij)
        in
        [ and_fol with_init (bform_to_fol k) ]
      and ensures =
        (* disjunction of exit-arc post-condition sharing the same pre-condition *)
        [
          List.fold_left (fun acc f -> or_fol acc (bform_to_fol f)) false_fol d;
        ]
      in
      { requires; ensures } :: s)
    m []
