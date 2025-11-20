open HardyFrontEnd.Syntax
open MiddleParser.HoaSyntax
open HardyMisc.Utils

let boola_of_label_expr (f_string: string -> BAAtom.t) (f_int: int ->BAAtom.t) : label_expr -> BoolA.t =
  let rec aux : label_expr -> BoolA.t =
  function
  | BoolLabel true -> True
  | BoolLabel false -> False 
  | IntLabel  n -> Atom (f_int n)
  | NameLabel s -> Atom (f_string s)
  | ConjLabel (l1,l2) -> And (aux l1,aux l2)
  | DisjLabel (l1,l2) -> Or (aux l1, aux l2)
  | NotLabel l -> Not (aux l)
  in aux



  type hoa_vdata = {acceptant: bool; start:bool}


module Vertex : Graph.Sig.COMPARABLE with type t = string * hoa_vdata
 = struct
  (* states are just labels and whether they are acceptant *)
  type t = string * hoa_vdata

  let compare s1 s2 = String.compare (fst s1) (fst s2)
  let hash s = String.hash (fst s)
  let equal s1 s2 = String.equal (fst s1) (fst s2)
end

module Arc : Graph.Sig.ORDERED_TYPE_DFT with type t = BoolA.disjunction = struct
  type t =   BoolA.disjunction

  let compare = Stdlib.compare
  let default : t =  BoolA.(mk_disj (DisjBoolA.empty))
end


module Make (Atoms : Atom.S with type 'a t = 'a) :
  BuchiSig.S with type E.label = BoolA.disjunction 
              and type init_val = hoa 
              and type 'a Atoms.t = 'a
  =
struct
  include Graph.Imperative.Digraph.ConcreteLabeled (Vertex) (Arc)

  module Atoms = Atoms

  type init_val = hoa
  type vdata = hoa_vdata

  let acceptant v = (snd v).acceptant
  let is_start_node (v : V.t) = (snd v).start

  let create (hoa : hoa) : t =
    let start = List.find_map (function Start [x] -> Some x | _ -> None ) hoa.header.items |> Option.get in

    let ap_labels= List.find_map (function Atomic (_,l) -> Some l | _ -> None ) hoa.header.items |> Option.get |> List.mapi (fun i x -> (i,x)) in
    let get_edge_label n = 
      (* Format.printf "[%a]@." (Format.pp_print_list (fun fmt (i,s) -> Format.fprintf fmt "(%i,%s)" i s)) ap_labels; *)
      match List.assoc_opt n ap_labels with
      | Some x -> x
      |None -> 
          (* no label, make the atom map to true *)
          (* Format.printf "no label for atom: %i\n" n; *)
          Atoms.add_and_get Fol.true_fol |> snd
      
    in
    let g = create ~size:(List.find_map (function States n -> Some n | _ -> None) hoa.header.items |> Option.get) () in
    List.iter
      (fun (state,edges) ->
        List.iter (fun edge ->
          let src = V.create  (string_of_int state.state_number, {start=state.state_number = start; acceptant=state.state_acc_sets <> []}) 
          and label = BoolA.(edge.edge_label |> Option.get |> boola_of_label_expr (fun _ -> failwith "got labeled name") get_edge_label |> nnf_of_boola |> dnf_of_boola)
          and dst = 
            let state = 
              (* fixme: once a vertex is added, it cannot be updated (-> use the vdata properly with the lib).
                workaround: lookup the next vertex to get its data right away
              *)
              List.find (fun ({state_number;_},_) -> state_number = List.hd edge.edge_dst) hoa.body |> fst in 
            V.create (string_of_int state.state_number, {start=state.state_number = start; acceptant=state.state_acc_sets <> []}) in
          
          let e =
            E.create
              src
              label
              dst
          in
          add_edge_e g e;
        ) edges;
        )
      hoa.body;
    g

  let pp_vertex fmt s = Format.pp_print_string fmt (fst s)

  let id_of_vertex = Format.asprintf "%a" pp_vertex
  (* let rec string_of_edge (f : label_expr) = match f with
  | BoolLabel b -> string_of_bool b
  | IntLabel i -> string_of_int i
  | NameLabel s -> s
  | ConjLabel (e1, e2) -> Printf.sprintf "%s & %s" (string_of_edge e1) (string_of_edge e2)
  | DisjLabel (e1, e2) -> Printf.sprintf "%s & %s" (string_of_edge e1) (string_of_edge e2)
  | NotLabel e -> "~" ^ string_of_edge e *)
  

  let pp_atom_full = fun fmt s -> HardyFrontEnd.Printer.(pp_fol (pp_pred (pp_exp pp_hist)) pp_ty) fmt (Atoms.get s |> snd) 
  let pp_atom_short = fun fmt s -> Format.pp_print_string fmt (Atoms.get s |> fst)

  let pp_edge fmt (f : E.label) = 
    let conjs = BoolA.DisjBoolA.to_seq f.disjuncts in 

    let nb_lit = Seq.fold_left (fun acc x -> Int.add acc @@ BoolA.AtomicBASet.cardinal x.conjuncts) 0 conjs in
    (* serves as a hint to decide if atoms should be printed in short or full form *)
    let pp_atom = (if nb_lit > 6 then pp_atom_short else pp_atom_full) in

    Format.fprintf fmt "%a" (BoolA.pp_dnf_boola pp_atom) f

  let get_vdata = snd

  let get_edge_type (e : E.label) =
    let open BuchiSig in
    match  BoolA.DisjBoolA.cardinal e.disjuncts with 
    | 0 -> Universal 
    | 1 when  BoolA.(AtomicBASet.exists (function False -> true | _ -> false) (DisjBoolA.choose e.disjuncts).conjuncts) -> Blocking 
    | _ -> Unknown
end

module SpinHoaOutput : Sig.ToolSig with 
        type input = string HardyFrontEnd.Syntax.Ltl.ltl and
        type output = hoa
= struct
  open HardyFrontEnd
  type input = string HardyFrontEnd.Syntax.Ltl.ltl
  type output = hoa

    let call (i : Cli.info) (hoa_file : string -> string) (f : string Syntax.Ltl.ltl) : output =
      let open Format in
      let hoa_file = hoa_file ".hoa" in
    let to_spin = Printer.(pp_ltl pp_print_string pp_ltl_binop_spin pp_ltl_unnop_spin) in
    let cmd =
      Filename.quote_command "ltl2tgba"
        [ "-B"; asprintf "%a" to_spin f]
        ~stdout:hoa_file ~stderr:(hoa_file ^ ".err")
    in
    if i.verbose then printf "ltl2tgba command line : %s@." cmd;
    let ret = Sys.command cmd in
    if ret <> 0 then
      failwith (sprintf "non-0 exit-code (%i) from ltl2tgba@." ret)
    else MiddleParser.HoaParsing.parse_automaton hoa_file
end
