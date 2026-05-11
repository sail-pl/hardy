open HardyFrontEnd.Syntax
open FrontParser.SharedSyntax
(* open MiddleParser.Labeling *)
open MiddleParser.HoaSyntax
open MiddleParser.HoaHelpers
open HardyMisc.Utils


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
    and type vdata = (name: string * acceptant: bool * start:bool)
    (* and type TAtom.t = TAtom.t *)
    (* and type 'a FAtom.t = 'a  *)
    (* and type FAtom.atom = FAtom.atom *)
    (* and type 'a FAtom.data = 'a FAtom.data  *)
  =
struct
  (* module TAtom = TAtom *)

  module State = struct

    (* states are just labels and whether they are acceptant *)
    type t = string * (name: string * acceptant: bool * start:bool)


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
  type vdata = (name: string * acceptant: bool * start:bool)

  let is_acceptant (_,(~acceptant,..) : V.t) = acceptant
  let is_start_node (_,(~start,..) : V.t) = start

  let create (hoa : hoa) : t =
    if not @@ List.mem "deterministic" @@ get_props hoa then
      Format.printf "WARNING: automaton not labeled as deterministic@."
    ; 
    (* automaton must have a supported acceptance condition  *)
    let [@warning "-4"] hoa = match get_acceptance hoa with 
      | (1, SetCond c) when not c.fin_occur ->
        List.iter (fun (st,_) -> 
          if not @@ List.mem c.set_number st.state_acc_sets then match st.state_acc_sets with
            | [] -> () (* non-acceptant set *)
            | h::_ ->
              failwith @@ Format.sprintf "malformed hoa: state %i has an incorrect acceptance set (got %i, expected %i)" 
                st.state_number 
                h
                c.set_number
        ) hoa.body; 
        hoa
      | (0, BoolAccept true) -> 
        (* any word is recognized, make all states acceptant *)
        let body = List.map (pair_map (Left (fun st -> {st with state_acc_sets=[0]}))) hoa.body in 
        {hoa with body}
      | _ -> failwith "unsupported acceptance condition"

    in
    let starting_node = match get_start hoa with 
      | [x] -> x 
      | [] -> failwith "no starting node" 
      | _ -> failwith "more than one starting node"
  
    in

    let true_atom = Atom.register_atom Label.tt |> snd (*|> TAtom.create *) in
    let false_atom = Atom.register_atom Label.ff  |> snd (*|> TAtom.create*) in

    let get_edge_label n : string = 
      (* Format.printf "[%a]@." (Format.pp_print_list (fun fmt (i,s) -> Format.fprintf fmt "(%i,%s)" i s)) ap_labels; *) 
      match List.assoc_opt n @@ get_atoms hoa with
      | Some id -> (* TAtom.create*) id
      | None -> 
          (* no label, make the atom map to true *)
          Format.printf "no label for atom: %i, mapping to 'true'\n" n;
          true_atom 
    in
    let g = create ?size:(get_num_states hoa) () in
    List.iter
      (fun (state,edges) ->
        List.iter (fun edge ->
          let start,acceptant = state.state_number = starting_node, state.state_acc_sets <> [] in 
          let src = 
            let name = string_of_int state.state_number in
            V.create  (string_of_int state.state_number, (~name,~acceptant,~start)) 
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
            let name,start,acceptant = 
              string_of_int state.state_number,
              state.state_number = starting_node, 
              state.state_acc_sets <> [] in 
            V.create (string_of_int state.state_number, (~name,~acceptant,~start)) in
          
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
  let pp_vertex fmt (s,_ : vertex) = Format.pp_print_string fmt s

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
    let to_spin = Printer.(pp_ltl pp_print_string pp_ltl_binop_spin pp_ltl_unnop_spin) in
    let f = asprintf "%a" to_spin f in

    let proc = Shexp_process.(Let_syntax.(
        find_executable_exn "ltlfilt" >>= fun ltlfilt ->
        (* ensure this is a safety formula *)
        run_exit_status ltlfilt [ "--safety" ; "-f" ; f ]
        (* get the automaton *)
        |+ (find_executable_exn "ltl2tgba" 
        >>= fun ltl2tgba ->
        run ltl2tgba  [ "-B" ; "-D"; "-x sat-minimize" ; f])
        (* ensure it is deterministic *)
        |+ run_exit_status "autfilt" ["-D" ; "--is-deterministic"; "--trust-hoa=false"]  (* ensures the automaton is deterministic *)
        |> stdout_to hoa_file
        |> if i.verbose then stderr_to (hoa_file ^ ".err") else Fun.id
      )
      )
    in
    let eval x = if i.verbose then Shexp_process.Logged.eval x else Shexp_process.eval x in
    let [@warning "-4"] () = match eval proc |> fst |> fst with
    | Exited 0 -> ()
    | _ -> if i.ignore_unsafe then 
        Format.printf "WARNING: formula '%s' is unsafe@." f 
       else failwith @@ Format.asprintf "'%s' is not a safety formula" f
      in
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
    
    let to_spin ppltl = Printer.(pp_ltl ppltl pp_ltl_binop_spin pp_ltl_unnop_spin) in
    let f_past = asprintf "%a" 
      Printer.(to_spin @@ fun fmt -> Format.fprintf fmt "(%a)" (pp_pltl_default pp_print_string)) f in
    let f_nopast = asprintf "%a" 
      Printer.(to_spin @@ fun fmt x -> fprintf fmt "p%i" (Hashtbl.hash x.value) ) f in
    
    let proc = Shexp_process.(Let_syntax.(
      find_executable_exn "ltlfilt" 
      >>= fun ltlfilt ->
      (* ensure this is a safety formula *)
      (run_exit_status ltlfilt [ "--safety" ; "-f" ; f_nopast ]
      |> Shexp_process.capture [Stdout])
      >>= fun (exit_status,_) -> 
      (* get the automaton *)
      find_executable_exn "pltl2tgba" 
      >>= fun pltl2tgba ->
      run pltl2tgba ["-f" ; f_past] 
      (* ensure it is deterministic *)
      |- run_exit_status "autfilt" ["-D" ; "-B" ; "--is-deterministic"; "--trust-hoa=false"]  (* ensures the automaton is deterministic *)
        |> stdout_to hoa_file
        |> (if i.verbose then stderr_to (hoa_file ^ ".err") else Fun.id)
      |+ return exit_status
      )
      )
    in
    let eval x = if i.verbose then Shexp_process.Logged.eval x else Shexp_process.eval x in
    let [@warning "-4"] () = match eval proc with
    | Exited 0,Exited 0 -> ()
    | Exited 1,_ -> 
      if i.ignore_unsafe then 
        Format.printf "WARNING: formula '%s' is unsafe@." f_past
      else failwith @@ Format.asprintf "'%s' is not a safety formula" f_past
    | _, _ -> failwith @@ Format.asprintf "autfilt check didn't pass for '%s'" f_past
    in
    (* if i.verbose then  
    print_string @@ "command output: " ^ Shexp_process.eval proc; *)
    let a = MiddleParser.HoaParsing.parse_automaton hoa_file in     
    if not i.dump_automata then Sys.remove hoa_file;   
    a

end
