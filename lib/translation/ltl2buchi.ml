module L = Lexing
(* module A = Automaton *)
open Bucchi
open TranslateUtils
open ArduinoSyntax.Locations
(* open ArduinoSyntax.Types *)
open ArduinoSyntax.Fol
open ArduinoSyntax.Ltl
open ArduinoSyntax.Syntax
open ArduinoSyntax.Printer
open ArduinoSyntax.PromelaSyntax
(* module Atoms = Atom()
module Buchi = A.Buchi(Atoms)
module DotG = A.BuchiDot(Buchi)
module PG = A.BuchiProd(Buchi)(Atoms)
module DotPG = A.BuchiDot(PG) *)
open ArduinoExternals.Ltl2ba
open Graph

module type AtomSig = sig
  val get : string -> string * expr fol
  val subst : string -> string
  val add : expr fol -> string * string
end

exception Atom_not_found of string

module Atom () : AtomSig = struct
  (* key is a hash of fol, value is a short name for fol + fol itself*)
  let atomic_bindings : (int, string * expr fol) Hashtbl.t = Hashtbl.create 100
  let cnt = ref 0

  let get (s : string) =
    let k = String.(sub s 2 (length s - 2) |> int_of_string) in
    try 
      Hashtbl.find atomic_bindings k
  with Not_found -> raise (Atom_not_found s)

  let sub_atom_in_str f =
    let open Str in
    let r = regexp {|f_\([0-9]+\)|} in
    global_substitute r (fun m -> matched_string m |> f)

  let subst =
    sub_atom_in_str (fun s ->
        let _, inv = get s in
        string_of_fol inv)

  let add (f : expr fol) =
    let label = Format.sprintf "f_%i" in

    (* we must get the same atom if the formulas are syntactically equal*)
    let key = Hashtbl.hash (determ_fol f) in

    match Hashtbl.find_opt atomic_bindings key with
    | None ->
        let short_name = "F" ^ string_of_int !cnt in
        Hashtbl.add atomic_bindings key (short_name, f);
        incr cnt;
        (short_name, label key)
    | Some (sn, _) -> (sn, label key)
end

module Vertex : Sig.COMPARABLE with type t = string = struct
  (* states are just labels *)
  type t = string

  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

(* output of ltl2ba with formula for each arc *)
module Arc : Sig.ORDERED_TYPE_DFT with type t = AS.bform = struct
  type t = AS.bform

  let compare = Stdlib.compare
  let default = AS.True
end

module BuchiClaim (Atoms : AtomSig) :
  BuchiSig with type E.label = AS.bform and type init_val = AS.neverclaim =
struct
  include Imperative.Digraph.ConcreteLabeled (Vertex) (Arc)

  type init_val = AS.neverclaim

  let acceptant v = List.hd String.(split_on_char '_' v) = "accept"
  let is_start_node (v : V.t) = String.ends_with (V.label v) ~suffix:"init"

  let create (claim : AS.neverclaim) : t =
    let open ArduinoSyntax.PromelaSyntax in
    let g = create ~size:(List.length claim.pml_states) () in
    List.iter
    (fun tr ->
      let e = E.create (V.create (tr.pml_src.pml_state)) tr.pml_form (V.create tr.pml_dst.pml_state) in
      add_edge_e g e)
      claim.pml_transitions;
    g

  let string_of_vertex v =
    match String.split_on_char '_' v with
    | "accept" :: [ n ] -> n (* acceptant state *)
    | s :: [] -> s (* non-acceptant state *)
    | _ as x ->
        failwith (Printf.sprintf "bad label name : %s" (String.concat "" x))

  let id_of_vertex = string_of_vertex
  let string_of_edge (f : AS.bform) = AS.string_of_bform Atoms.subst f
end

module PArc : Sig.ORDERED_TYPE_DFT with type t = AS.bform S.hoare_pair = struct
  type t = AS.bform S.hoare_pair

  let compare = Stdlib.compare
  let default = S.{ requires = AS.True; ensures = AS.True }
end


module BuchiProd
    (G : BuchiSig with type E.label = AS.bform)
    (Atoms : AtomSig) :
  BuchiSig with type init_val = G.t * G.t and type E.label = PArc.t = struct
  module MV =
    (* Util.DataV
       (struct type t = bool (* for marking treated states *) end) *)
      Util.CMPProduct (G.V) (G.V)
  (* /!\ make sure to always create vertices with the same argument order *)

  include Imperative.Digraph.ConcreteLabeled (MV) (PArc)

  type init_val = G.t * G.t

  let acceptant v =
    let l1, l2 = V.label v in
    G.acceptant l1 && G.acceptant l2

  let create (rely_a, guarantee_a) : t =
    let res = create ~size:G.(nb_vertex rely_a + nb_vertex guarantee_a) () in

    (* no vertex find function ?? *)
    let find_init_node g =
      G.fold_vertex
        (fun v acc ->
          match acc with
          | None -> if G.is_start_node v then Some v else None
          | v -> v)
        g None
      |> Option.get
    in

    (* the first node is made up of the first node from both automata *)
    let init_r, init_g = (find_init_node rely_a, find_init_node guarantee_a) in
    let init_node = V.create (init_r, init_g) in
    (* init queue with it *)
    let workq = Queue.create () in
    Queue.push init_node workq;

    while not (Queue.is_empty workq) do
      let curr_node = Queue.pop workq in

      let r, g = V.label curr_node in

      (* ... get all its out-transitions *)
      let r_out = G.succ_e rely_a r in
      let g_out = G.succ_e guarantee_a g in

      (* make the product of the destination node of the transitions *)
      List.iter
        (fun r ->
          List.iter
            (fun g ->
              let new_node = V.create G.(E.dst r, E.dst g) in
              (* add it to the list if not already treated *)
              if not (mem_vertex res new_node) then Queue.push new_node workq;
              (* make the curr_node -> new_node transition *)
              let label = S.{ requires = G.E.label r; ensures = G.E.label g } in
              let edge = E.create curr_node label new_node in
              add_edge_e res edge)
            g_out)
        r_out;
      ()
    done;
    res

  let is_start_node (v : V.t) =
    let l1, l2 = V.label v in
    G.is_start_node l1 && G.is_start_node l2

  let string_of_vertex v =
    let l1, l2 = V.label v in
    Format.sprintf "{pre_%s \n post_%s}"
      G.(string_of_vertex (V.label l1))
      G.(string_of_vertex (V.label l2))

  let id_of_vertex v =
    let l1, l2 = V.label v in
    Format.sprintf "pre_%s_post_%s"
      G.(string_of_vertex (V.label l1))
      G.(string_of_vertex (V.label l2))

  let string_of_edge (e : E.label) =
    Format.sprintf "requires: %s \n ensures : %s"
      (e.requires |> AS.string_of_bform Atoms.subst)
      (e.ensures |> AS.string_of_bform Atoms.subst)
end


module Atoms = Atom()
module Buchi = BuchiClaim(Atoms)
module DotG = BuchiDot(Buchi)
module PG = BuchiProd(Buchi)(Atoms)
module DotPG = BuchiDot(PG)

(* Move options info and output file to ltl2ba *)
(** {1 Build Bucchi Automaton from string formula } *)

let string_of_ltl_full = string_of_ltl (fun p -> Atoms.add p |> snd)
let string_of_ltl_short = string_of_ltl (fun p -> Atoms.add p |> fst)

let bform_to_fol : bform -> expr fol = 
  fol_of_bform (fun a -> Atoms.get a |> snd)


(** [compute_automaton f] builds a bucchi from the string formula [f] 
    where atomes are names *)
let buchi_of_ltl (i : info) (name : string) (f : expr fol ltl) : Buchi.t = 
  let output_file name ext = Filename.(concat i.outdir (name ^ ext)) in
  let f_str = string_of_ltl_full f in
    (if i.verbose then
      let f_str_short = string_of_ltl_short f in
        Format.printf "\n %s formula : \n%s\n" name f_str_short);
        let never_file = output_file name ".never" in
        let () = generate_claim i never_file f_str 
        in let auto = read_claim never_file |> Buchi.create in
        Out_channel.with_open_text (output_file name ".dot") (fun o ->
            DotG.output_graph o auto);
        auto
      
(** Builds the product automaton from two formulas *)
  let product_automaton (i : info) (req : expr fol ltl option) (ens : expr fol ltl option) =
    let output_file name ext = Filename.(concat i.outdir (name ^ ext)) in
      let true_if_none = Option.value ~default:(mk_dummy_loc LTL_True) in
      let rely_a = true_if_none req |> buchi_of_ltl i "rely" in
      let guarantee_a =
        true_if_none (ltl_conjunction req ens) |> buchi_of_ltl i "guarantee"
      in let prod_a = PG.create (rely_a, guarantee_a) in
        Out_channel.with_open_text (output_file "product" ".dot") 
          (fun o -> DotPG.output_graph o prod_a);
        prod_a

