open MiddleParser.HoaSyntax
open MiddleParser.SyntaxCommon

let rec bform_of_label_expr : label_expr -> string bform = function
  | BoolLabel true -> True
  | BoolLabel false -> False 
  | IntLabel  n -> Atom (string_of_int n)
  | NameLabel s -> Atom s
  | ConjLabel (l1,l2) -> And (bform_of_label_expr l1,bform_of_label_expr l2)
  | DisjLabel (l1,l2) -> Or (bform_of_label_expr l1, bform_of_label_expr l2)
  | NotLabel l -> Not (bform_of_label_expr l)



module Vertex : Graph.Sig.COMPARABLE with type t = bool * string = struct
  (* states are just labels *)
  type t = bool * string

  let compare s1 s2 = String.compare (snd s1) (snd s2)
  let hash s = String.hash (snd s)
  let equal s1 s2 = String.equal (snd s1) (snd s2)
end


module Make (Atoms : Atom.S with type 'a t = 'a) :
  BuchiSig.S with type E.label = string bform and type init_val = hoa =
struct
  include Graph.Imperative.Digraph.ConcreteLabeled (Vertex) (Nc2ba.Arc)

  type init_val = hoa
  type vdata = unit

  let acceptant _ = true
  let is_start_node (v : V.t) = fst v

  let create (hoa : hoa) : t =
    let start = List.find_map (function Start [x] -> Some x | _ -> None ) hoa.header.items |> Option.get in
    let g = create ~size:(List.find_map (function States n -> Some n | _ -> None) hoa.header.items |> Option.get) () in
    List.iter
      (fun (state,edges) ->
        List.iter (fun edge ->
          let e =
            E.create
              (V.create  (state.state_number = start , string_of_int state.state_number))
              (edge.edge_label |> Option.get |> bform_of_label_expr)
              (V.create (List.hd edge.edge_dst = start,string_of_int @@ List.hd edge.edge_dst))
          in
          add_edge_e g e;
        ) edges;
        )
      hoa.body;
    g

  let string_of_vertex (v:vertex) =
    match String.split_on_char '_' (snd v) with
    | "accept" :: [ n ] -> n (* acceptant state *)
    | s :: [] -> s (* non-acceptant state *)
    | _ -> snd v (* others *)

  let id_of_vertex = string_of_vertex
  (* let rec string_of_edge (f : label_expr) = match f with
  | BoolLabel b -> string_of_bool b
  | IntLabel i -> string_of_int i
  | NameLabel s -> s
  | ConjLabel (e1, e2) -> Printf.sprintf "%s & %s" (string_of_edge e1) (string_of_edge e2)
  | DisjLabel (e1, e2) -> Printf.sprintf "%s & %s" (string_of_edge e1) (string_of_edge e2)
  | NotLabel e -> "~" ^ string_of_edge e *)
  
  let string_of_edge (f : E.label) = string_of_bform Atoms.subst f

  let get_vdata _ = ()

  let get_edge_type (e : E.label) =
    let open BuchiSig in
    match e with True -> Universal | False -> Blocking | _ -> Unknown
end
