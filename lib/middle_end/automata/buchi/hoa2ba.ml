open HardyFrontEnd.Syntax
open FrontParser.SharedSyntax
(* open MiddleParser.Labeling *)
open MiddleParser.HoaSyntax



module Make
  (* (TAtom: 
    TseitinAtomSig 
    (* was used to force formulas into cnf, creating additional predicates to counter exponential size *)
  ) *)
  (Atom : Atom.S with 
    type 'a t = 'a 
  (* formula level atoms *)
  )
  (Label : BoolA with type 'a t = Atom.atom
    (* arc labeling: a boolean algebra of propositions *)
  ) : 
  BuchiSig.S  
    with type init_val = hoa  
    and type E.label = string bool_a
    (* and type TAtom.t = TAtom.t *)
    (* and type 'a FAtom.t = 'a  *)
    (* and type FAtom.atom = FAtom.atom *)
    (* and type 'a FAtom.data = 'a FAtom.data  *)
  =
struct
  (* module TAtom = TAtom *)

  type hoa_vdata = {acceptant: bool; start:bool}

  module State = struct

    (* states are just labels and whether they are acceptant *)
    type t = string * hoa_vdata


    let compare s1 s2 = String.compare (fst s1) (fst s2)
    let hash s = String.hash (fst s)
    let equal s1 s2 = String.equal (fst s1) (fst s2)
  end



  module Transition = struct
      type t =  string bool_a
      let compare = Stdlib.compare
      let default : t = True
  end

  include Graph.Imperative.Digraph.ConcreteLabeled (State) (Transition)

  type init_val = hoa
  type vdata = hoa_vdata

  let acceptant v = (snd v).acceptant
  let is_start_node (v : V.t) = (snd v).start

  let create (hoa : hoa) : t =
    let () = 
      let [@warning "-4"] props = List.filter_map (function Properties n -> Some n | _ -> None) hoa.header.items |> List.flatten in
      if not @@ List.mem "deterministic" props then
        failwith "non-deterministic automaton";
    in
    let [@warning "-4"] start = List.find_map (function Start [x] -> Some x | _ -> None ) hoa.header.items |> Option.get in

    let [@warning "-4"] ap_labels = List.find_map (function Atomic (_,l) -> Some l | _ -> None ) hoa.header.items |> Option.get |> List.mapi (fun i x -> (i,x)) in

      let true_atom = Atom.register_atom Label.tt |> snd (*|> TAtom.create *) in
      let false_atom = Atom.register_atom Label.ff  |> snd (*|> TAtom.create*) in

    let get_edge_label n : string = 
      (* Format.printf "[%a]@." (Format.pp_print_list (fun fmt (i,s) -> Format.fprintf fmt "(%i,%s)" i s)) ap_labels; *) 
      match List.assoc_opt n ap_labels with
      | Some id -> (* TAtom.create*) id
      | None -> 
          (* no label, make the atom map to true *)
          Format.printf "no label for atom: %i, mapping to 'true'\n" n;
          true_atom 
    in
    let [@warning "-4"] g = create ~size:(List.find_map (function States n -> Some n | _ -> None) hoa.header.items |> Option.get) () in
    List.iter
      (fun (state,edges) ->
        List.iter (fun edge ->
          let src = V.create  (string_of_int state.state_number, {start=state.state_number = start; acceptant=state.state_acc_sets <> []}) 
          and label = edge.edge_label |> Option.get |> map_formula (function 
            | BoolLabel true -> true_atom
            | BoolLabel false -> false_atom
            | IntLabel i ->  get_edge_label i
            | NameLabel _ -> failwith "got labeled name"
          ) 
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
  

  let pp_atom_full = fun fmt s ->
      (* let name = TAtom.get_atom_id s in
      if TAtom.is_generated s then 
        Format.fprintf fmt "g%s" name
      else  *)
        Label.pp (fun _ _ -> ()) fmt (s |> Atom.get_atom |> snd)

  
  let pp_atom_short = fun fmt s -> 
      (*let name = TAtom.get_atom_id s in
      if TAtom.is_generated s then 
        Format.fprintf fmt "g%s" name
      else*)
        Format.pp_print_string fmt (s |> Atom.get_atom |> fst |> fun s -> "a" ^ s) 


  let pp_edge fmt (f : E.label) = 
    let pp_atom = (if formula_depth f > 4 then pp_atom_short else pp_atom_full) in
    Format.(fprintf fmt "%a" (pp_boola pp_atom) f)
  let get_vdata = snd

  let get_edge_type (_ : E.label) = BuchiSig.Unknown
end

module SpinHoaOutput : AutSig.ToolSig with 
        type input = string HardyFrontEnd.Syntax.Ltl.ltl and
        type output = hoa
= struct
  open HardyFrontEnd
  type input = string HardyFrontEnd.Syntax.Ltl.ltl
  type output = hoa

  let call (i : Cli.config) (hoa_file : string -> string) (f : string Syntax.Ltl.ltl) : output =
    let open Format in
    let hoa_file = hoa_file ".hoa" in
    let stderr = if i.verbose then Some (hoa_file ^ ".err") else None in
    let to_spin = Printer.(pp_ltl pp_print_string pp_ltl_binop_spin pp_ltl_unnop_spin) in
    let cmd =
      Filename.quote_command "ltl2tgba"
        [ "-B" ; "-D"; "-x sat-minimize" ; asprintf "%a" to_spin f]
        ~stdout:hoa_file ?stderr
    in
    if i.verbose then printf "ltl2tgba command line : %s@." cmd;
    let ret = Sys.command cmd in
    if ret <> 0 then
      failwith (sprintf "non-0 exit-code (%i) from ltl2tgba@." ret)
    else 
      let a = MiddleParser.HoaParsing.parse_automaton hoa_file in 
      if not i.dump_automata then Sys.remove hoa_file;
      a
end


module PpLTLHoaOutput : AutSig.ToolSig with 
        type input = string Ppltl.pltl HardyFrontEnd.Syntax.Ltl.ltl and
        type output = hoa
= struct
  open HardyFrontEnd
  
  type input = string Ppltl.pltl HardyFrontEnd.Syntax.Ltl.ltl
  type output = hoa

  let call (i : Cli.config) (hoa_file : string -> string) (f : string Ppltl.pltl Syntax.Ltl.ltl) : output =
    let open Format in
    let hoa_file = hoa_file ".hoa" in
    
    let to_spin = Printer.(pp_ltl (pp_pltl_default pp_print_string) pp_ltl_binop_spin pp_ltl_unnop_spin) in
    
    
    let proc = Shexp_process.(Let_syntax.(
        find_executable_exn "pltl2tgba" >>= fun pltl2tgba ->
        run pltl2tgba [ "-f" ; asprintf "%a" to_spin f ] 
        |- run "autfilt" ["-D" ; "--is-deterministic"; "--trust-hoa=false"]  (* ensures the automaton is deterministic *)
        |> stdout_to hoa_file
        |> if i.verbose then stderr_to (hoa_file ^ ".err") else Fun.id
      )
      )
    in
    Shexp_process.eval proc;
    (* if i.verbose then  
    print_string @@ "command output: " ^ Shexp_process.eval proc; *)
    let a = MiddleParser.HoaParsing.parse_automaton hoa_file in     
    if not i.dump_automata then Sys.remove hoa_file;   
    a

end
