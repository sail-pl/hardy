open HardyFrontEnd
open Syntax.Fol
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

  module ConjBoolA = AtomicBASet
  type nonrec conjunction = ConjBoolA.t conjunction

  (** [disjunct_set] is the disjunctive normal form obtained from a [bool_algebra] formula *)

  module DisjBoolA = Set.Make (struct
    type t = conjunction

    let compare = Stdlib.compare
  end)

  type nonrec disjunction = DisjBoolA.t disjunction


  let rec dnf_of_boola (f:nnf_boola) : disjunction = mk_disj 
  (match f with
  | Atom a -> a |> ConjBoolA.singleton |> mk_conj |> DisjBoolA.singleton
  | And (f1, f2) -> 
    let f1 = dnf_of_boola f1 and f2 = dnf_of_boola f2 in 
    DisjBoolA.(fold (fun conj1 disj -> union disj (map (fun conj2 -> ConjBoolA.union conj1.conjuncts conj2.conjuncts |> mk_conj) f2.disjuncts)) f1.disjuncts empty) 
  | Or (f1, f2) -> DisjBoolA.union (dnf_of_boola f1).disjuncts (dnf_of_boola f2).disjuncts) 

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
      
  let pp_paren_atomic_boola f fmt (e : AtomicBASet.t) =
    let open Format in   
    match AtomicBASet.cardinal e with 0 -> pp_print_string fmt "true" | 1 -> f fmt e | _ -> fprintf fmt "(%a)" f e

  let pp_dnf_boola (pp_atom : Format.formatter -> string -> unit) fmt (s: disjunction) : unit =
    let open Format in
    pp_print_seq 
    ~pp_sep:(fun fmt () -> fprintf fmt " | ")
    (fun fmt {conjuncts} -> pp_paren_atomic_boola (pp_atomic_boola_set pp_atom) fmt conjuncts)
    fmt
    (DisjBoolA.to_seq s.disjuncts)

      
  let fol_of_dnf_boola (convert_atom : A.t -> ('a, 'b) fol) (f: disjunction) : ('a, 'b) fol =
    let disj = Seq.(
      DisjBoolA.to_seq f.disjuncts 
      |> map (fun {conjuncts} ->
          let fol_conj = AtomicBASet.to_seq conjuncts
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