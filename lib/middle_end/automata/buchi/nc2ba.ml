(* open MiddleParser.SyntaxCommon *)
open MiddleParser.NcSyntax
open HardyMisc.Utils

module Vertex : Graph.Sig.COMPARABLE with type t = string = struct
  (* states are just labels *)
  type t = string

  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

(* output of ltl2ba with formula for each arc *)
module Arc : Graph.Sig.ORDERED_TYPE_DFT with type t = BoolA.disjunction = struct
  type t =   BoolA.disjunction

  let compare = Stdlib.compare
  let default : t =  BoolA.(mk_disj (DisjBoolA.empty))
end

module Utils (G : Graph.Sig.I) = struct
  (* no vertex find function ??
    -> from the manual: 
    "you should better keep the vertices as long as you create them."
  *)
  exception Found of G.V.t

  let find_v_opt g i =
    try
      G.iter_vertex (fun v -> if G.V.label v = i then raise (Found v)) g;
      None
    with Found v -> Some v
end

module Make (Atoms : Atom.S with type 'a t = 'a) :
  BuchiSig.S with type E.label = BoolA.disjunction 
              and type init_val = neverclaim 
              and type 'a Atoms.t = 'a
=
struct
  include Graph.Imperative.Digraph.ConcreteLabeled (Vertex) (Arc)

  module Atoms = Atoms

  type init_val = neverclaim
  type vdata = unit

  let acceptant v = List.hd String.(split_on_char '_' v) = "accept"
  let is_start_node (v : V.t) = String.ends_with (V.label v) ~suffix:"init"

  let create (claim : neverclaim) : t =
    let g = create ~size:(List.length claim.pml_states) () in
    List.iter
      (fun tr ->
        let e =
          E.create
            (V.create tr.pml_src.pml_state)
             BoolA.(tr.pml_form |> nnf_of_boola |> dnf_of_boola)
            (V.create tr.pml_dst.pml_state)
        in
        add_edge_e g e)
      claim.pml_transitions;
    g

  let pp_vertex fmt v =
    (match String.split_on_char '_' v with
    | "accept" :: [ n ] -> n (* acceptant state *)
    | s :: [] -> s (* non-acceptant state *)
    | _ -> v (* others *)) |> Format.pp_print_string fmt

  let id_of_vertex = Format.asprintf "%a" pp_vertex

  let pp_atom_full = fun fmt s -> HardyFrontEnd.Printer.(pp_fol (pp_pred (pp_exp pp_hist)) pp_ty) fmt (Atoms.get s |> snd) 
  let pp_atom_short = fun fmt s -> Format.pp_print_string fmt (Atoms.get s |> fst)

  let pp_edge fmt (f : E.label) =
    let disjs = BoolA.DisjBoolA.to_seq f.disjuncts in 

    let nb_lit = Seq.fold_left (fun acc x -> Int.add acc @@ BoolA.AtomicBASet.cardinal x.conjuncts) 0 disjs in
    (* serves as a hint to decide if atoms should be printed in short or full form *)
    let pp_atom = (if nb_lit > 6 then pp_atom_short else pp_atom_full) in

    Format.fprintf fmt "%a" (BoolA.pp_dnf_boola pp_atom) f
    
    let get_vdata _ = ()

  let get_edge_type (e : E.label) =
    let open BuchiSig in
    match  BoolA.DisjBoolA.cardinal e.disjuncts with 
    | 0 -> Universal 
    | 1 when  BoolA.(AtomicBASet.exists (function False -> true | _ -> false) (DisjBoolA.choose e.disjuncts).conjuncts) -> Blocking 
    | _ -> Unknown
end

module SpinNcOutput : Sig.ToolSig with 
        type input = string HardyFrontEnd.Syntax.Ltl.ltl and
        type output = neverclaim
= struct
    open HardyFrontEnd
    type input = string HardyFrontEnd.Syntax.Ltl.ltl
    type output = neverclaim

    let call (i : Cli.info) (never_file : string -> string) (f : string Syntax.Ltl.ltl) : output =
    let open Format in
    let never_file = never_file ".never" in
    let to_spin = Printer.(pp_ltl pp_print_string pp_ltl_binop_spin pp_ltl_unnop_spin) in
    let cmd =
      Filename.quote_command "ltl2tgba"
        [ "-s"; asprintf "%a" to_spin f ]
        ~stdout:never_file ~stderr:(never_file ^ ".err")
    in
    if i.verbose then printf "ltl2tgba command line : %s@." cmd;
    let ret = Sys.command cmd in
    if ret <> 0 then
      failwith (sprintf "non-0 exit-code (%i) from ltl2tgba@." ret)
    else MiddleParser.NcParsing.parse_automaton never_file
end