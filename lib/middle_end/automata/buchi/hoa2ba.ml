open HardyFrontEnd.Syntax
open MiddleParser.HoaSyntax


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

module Arc : Graph.Sig.ORDERED_TYPE_DFT with type t = BoolA.disjunct_set = struct
  type t =   BoolA.disjunct_set

  let compare = Stdlib.compare
  let default : BoolA.disjunct_set =  BoolA.(mk_disjunct (DnfBASet.empty))
end


module Make (Atoms : Atom.S with type 'a t = 'a) :
  BuchiSig.S with type E.label = BoolA.disjunct_set and type init_val = hoa =
struct
  include Graph.Imperative.Digraph.ConcreteLabeled (Vertex) (Arc)

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
          and label = BoolA.(edge.edge_label |> Option.get |> boola_of_label_expr (fun _ -> failwith "got labeled name") get_edge_label |> nnf_of_boola |> dnf_of_boola  |> mk_disjunct)
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

  let string_of_vertex = fst

  let id_of_vertex = string_of_vertex
  (* let rec string_of_edge (f : label_expr) = match f with
  | BoolLabel b -> string_of_bool b
  | IntLabel i -> string_of_int i
  | NameLabel s -> s
  | ConjLabel (e1, e2) -> Printf.sprintf "%s & %s" (string_of_edge e1) (string_of_edge e2)
  | DisjLabel (e1, e2) -> Printf.sprintf "%s & %s" (string_of_edge e1) (string_of_edge e2)
  | NotLabel e -> "~" ^ string_of_edge e *)
  
  let string_of_edge (f : E.label) = Format.asprintf "%a"  (BoolA.pp_dnf_boola (fun fmt s -> Format.pp_print_string fmt (Atoms.get s |> fst))) f.boola_disjunct

  let get_vdata = snd

  let get_edge_type (e : E.label) =
    let open BuchiSig in
    match  BoolA.DnfBASet.cardinal e.boola_disjunct with 
    | 0 -> Universal 
    | 1 when  BoolA.(AtomicBASet.exists (function False -> true | _ -> false) (DnfBASet.choose e.boola_disjunct)) -> Blocking 
    | _ -> Unknown
end
