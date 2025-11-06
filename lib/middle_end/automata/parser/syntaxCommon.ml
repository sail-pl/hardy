open HardyFrontEnd.Syntax.Fol
open HardyMisc.Utils


module type BAAtomSig = sig
  type t

  val to_string : t -> string
end


module BoolAlgebra(A : BAAtomSig) = struct
(** [bool_algebra] is the generic labeling of edges and/or vertices *)

  type t =
    | True
    | False
    | Atom of A.t
    | And of t * t
    | Or of t *t
    | Not of t


  type atomic_boola = 
  | True
  | False
  | Atom of A.t
  | NegAtom of A.t

  type nnf_boola = 
  | And of nnf_boola * nnf_boola
  | Or of nnf_boola * nnf_boola
  | Atom of atomic_boola


  let rec nnf_of_boola : t -> nnf_boola = function
  | True -> Atom True
  | False -> Atom False
  | Atom a -> Atom (Atom a)
  | Not f -> (match f with
    | True -> Atom False
    | False -> Atom True
    | Not f' -> nnf_of_boola f'
    | Atom a -> Atom (NegAtom a)
    | And (f1,f2) -> Or (nnf_of_boola (Not f1), nnf_of_boola (Not f2))
    | Or (f1,f2) -> And (nnf_of_boola (Not f1), nnf_of_boola (Not f2))
  )
  | And (f1,f2) -> And (nnf_of_boola f1,nnf_of_boola f2)
  | Or (f1,f2) -> Or (nnf_of_boola f1,nnf_of_boola f2)




  module AtomicBASet = Set.Make (struct
    type t = atomic_boola

    let compare = Stdlib.compare
  end)

  module DnfBASet = Set.Make (struct
    type t = AtomicBASet.t

    let compare = Stdlib.compare
  end)


  (** [disjunct_set] is the disjunctive normal form obtained from a [bool_algebra] formula *)

  (* an empty conjunct_set is the same as the singleton {true} *)
  type conjunct_set = { boola_conjunct : AtomicBASet.t }

  (* an empty disjunct_set is the same as the singleton {false}*)
  type disjunct_set = { boola_disjunct : DnfBASet.t }

  let mk_conjunct boola_conjunct = {boola_conjunct}
  let mk_disjunct boola_disjunct = {boola_disjunct}



  let rec dnf_of_boola (f:nnf_boola) : DnfBASet.t = (match f with
  | Atom a -> a |> AtomicBASet.singleton |> DnfBASet.singleton
  | And (f1, f2) -> 
    let f1 = dnf_of_boola f1 and f2 = dnf_of_boola f2 in 
    DnfBASet.(fold (fun conj1 disj -> union disj (map (AtomicBASet.union conj1) f2)) f1 empty)
  | Or (f1, f2) -> DnfBASet.union (dnf_of_boola f1) (dnf_of_boola f2))



  (* let ( <-> ) f1 f2 = And (Or (Not f1, f2), Or (Not f2, f1))
  let ( --> ) f1 f2 = Or (Not f1, f2) *)

  (* let rec map_bform_atom : type a b. (a -> b) -> a bool_algebra -> b bool_algebra =
  fun m -> function
    | Atom a -> Atom (m a)
    | And (b1, b2) -> And (map_bform_atom m b1, map_bform_atom m b2)
    | Or (b1, b2) -> Or (map_bform_atom m b1, map_bform_atom m b2)
    | Not b -> Not (map_bform_atom m b)
    | (True | False) as x -> x *)

  (* let paren_bform f b = match b with  And _ | Or _  -> Format.sprintf "(%s)" (f b) | _ -> f b *)


  let pp_atomic_boola (pp_atom : Format.formatter -> string -> unit) fmt : atomic_boola -> unit = 
    let open Format in   
    function
    | True -> pp_print_string fmt "true"
    | False -> pp_print_string fmt "false"
    | Atom a -> fprintf fmt "%a" pp_atom (A.to_string a)
    | NegAtom a -> fprintf fmt "~%a" pp_atom (A.to_string a)

  let pp_atomic_boola_set (pp_atom : Format.formatter -> string -> unit) fmt (s:AtomicBASet.t) : unit = 
    let open Format in   
    pp_print_seq 
      ~pp_sep:(fun fmt () -> fprintf fmt " & ")
      (pp_atomic_boola pp_atom)
      fmt
      (AtomicBASet.to_seq s)

  let pp_dnf_boola (pp_atom : Format.formatter -> string -> unit) fmt (s:DnfBASet.t) : unit =
    let open Format in
    pp_print_seq 
    ~pp_sep:(fun fmt () -> fprintf fmt " | ")
    (fun fmt -> fprintf fmt "(%a)" (pp_atomic_boola_set pp_atom))
    fmt
    (DnfBASet.to_seq s)

      
  let fol_of_dnf_boola (convert_atom : A.t -> ('a, 'b) fol) (f: disjunct_set) : ('a, 'b) fol =
    let disj = Seq.(
      DnfBASet.to_seq f.boola_disjunct 
      |> map (fun conj ->
          let fol_conj = AtomicBASet.to_seq conj
            |> map (
              function
              | True -> mk_dummy_loc FOL_True
              | False -> mk_dummy_loc FOL_False
              | Atom s -> convert_atom s
              | NegAtom s -> mk_dummy_loc @@ FOL_StdUnary (LNot, (convert_atom s))
            )
            |> List.of_seq in
            mk_dummy_loc @@ FOL_StdNary (LAnd, fol_conj)
            )
        )
      |> List.of_seq
    in
    mk_dummy_loc (FOL_StdNary (LOr, disj))

end