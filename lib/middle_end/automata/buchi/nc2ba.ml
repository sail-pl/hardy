open HardyFrontEnd.Syntax
open MiddleParser.SyntaxCommon
open MiddleParser.NcSyntax

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

module Make
  (TAtom: TseitinAtomSig)
  (FAtom : Atom.S with 
    type 'a t = 'a and 
    type _ data = Instant.min_nb_instants
    and type qty = Shared.base_ty
    and type ty = Instant.instant option * Shared.ty
  ) :
  BuchiSig.S with 
    type init_val = neverclaim  and 
    type E.label = BoolAlgebra(TAtom).t and 
    type TAtom.t = TAtom.t and 
    type 'a FAtom.t = 'a and 
    type _ FAtom.data = Instant.min_nb_instants and
    type FAtom.ty = Instant.instant option * Shared.ty and 
    type FAtom.qty = Shared.base_ty
  =
struct
  module FAtom = FAtom
  module TAtom = TAtom
  module BA = BoolAlgebra(TAtom)

  module State = struct
  (* states are just labels *)
    type t = string

    let compare = String.compare
    let hash = String.hash
    let equal = String.equal
  end


  (* output of ltl2ba with formula for each arc *)
  module Transition = struct
    type t =   BA.t

    let compare = Stdlib.compare
    let default : t =  True
  end

  include Graph.Imperative.Digraph.ConcreteLabeled (State) (Transition)

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
            (map_eba TAtom.create tr.pml_form)
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

  let pp_atom_full = fun fmt s -> HardyFrontEnd.Printer.(pp_fol (pp_pred (pp_exp (fun fmt (x,(y,_)) -> pp_hist fmt (x,y)))) pp_base_ty) fmt ( s |> TAtom.get_atom_id |> FAtom.get_atom |> snd) 
  let pp_atom_short = fun fmt s -> Format.pp_print_string fmt ( s |> TAtom.get_atom_id |> FAtom.get_atom |> fst) 


  let pp_edge fmt (f : E.label) = 
    let nb_lit = 
      let rec aux f = 
        fold_eba (fun f -> match f with 
        | And (f1,f2) | Or (f1,f2)  -> fun _ -> max (aux f1) (aux f2)
        | _ -> Lazy.map_val ((+) 1)
        ) (fun _ -> Lazy.map_val ((+) 1)) (Lazy.from_val 0) f 
      in aux f |> Lazy.force_val
    in
    (* serves as a hint to decide if atoms should be printed in short or full form *)
    let pp_atom = (if nb_lit > 6 then pp_atom_short else pp_atom_full) in
    Format.(fprintf fmt "%a" (pp_eba pp_atom) f)
  let get_vdata _ = ()

  let get_edge_type (_ : E.label) = BuchiSig.Unknown
end

module Ltl2baNcOutput : Sig.ToolSig with 
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
      Filename.quote_command "ltl2ba"
        [ "-f"; asprintf "%a" to_spin f ]
        ~stdout:never_file ~stderr:(never_file ^ ".err")
    in
    if i.verbose then printf "ltl2ba command line : %s@." cmd;
    let ret = Sys.command cmd in
    if ret <> 0 then
      failwith (sprintf "non-0 exit-code (%i) from ltl2ba@." ret)
    else MiddleParser.NcParsing.parse_automaton never_file
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