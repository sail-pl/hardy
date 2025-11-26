open HardyFrontEnd
open Syntax.Fol
open HardyMisc.Utils

type 'a eba =
  | True
  | False
  | Atom of 'a
  | And of 'a eba * 'a eba
  | Or of 'a eba * 'a eba
  | Not of 'a eba

let rec map_eba fa = function
| True -> True
| False -> False
| Atom x -> Atom (fa x)
| And (f1,f2) -> And (map_eba fa f1,map_eba fa f2)
| Or (f1,f2) -> Or (map_eba fa f1,map_eba fa f2)
| Not f -> Not (map_eba fa f) 

let rec pp_boola (pp_atom : Format.formatter -> 'a -> unit) fmt : 'a eba -> unit =
    let open Format in 
    function
    | True -> pp_print_string fmt "true"
    | False -> pp_print_string fmt "false"
    | Atom a -> pp_atom fmt a
    | And (f1,f2) -> fprintf fmt "(%a & %a)" (pp_boola pp_atom) f1 (pp_boola pp_atom) f2
    | Or (f1,f2) -> fprintf fmt "(%a || %a)" (pp_boola pp_atom) f1 (pp_boola pp_atom) f2
    | Not f -> fprintf fmt "~(%a)" (pp_boola pp_atom) f


module type TseitinAtomSig = sig
  include Msat_tseitin.Arg

  val create : string -> t
  val get_atom_id : t -> string

  val is_neg : t -> bool
  val is_generated : t -> bool
end


module BoolAlgebra(A : TseitinAtomSig) = struct
(** [bool_algebra] is the generic labeling of edges and/or vertices *)

  type t = A.t eba 
  
  module Tseintin = Msat_tseitin.Make (A)

  let to_cnf (f : t) : A.t cnf  = 
    let rec to_tseitin : t -> Tseintin.t = 
      let open Tseintin in function
      | True -> f_true
      | False -> f_false
      | And (f1,f2) -> make_and [to_tseitin f1; to_tseitin f2]
      | Or (f1,f2) -> make_or [to_tseitin f1; to_tseitin f2]
      | Atom a -> make_atom a
      | Not f -> make_not (to_tseitin f)
    in 
    (Tseintin.make_cnf (to_tseitin f) |> List.map mk_disj) |> mk_conj


    let pp_paren_atomic_boola f fmt  = 
    let open Format in   
    function [] -> pp_print_string fmt "" | [x] -> f fmt [x] | l -> fprintf fmt "(%a)" f l

    let pp_cnf_boola f fmt (s: A.t cnf)  : unit =
    let open Format in
      pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt " ∧ ")
      (fun fmt {disjuncts} -> 
        pp_paren_atomic_boola 
        (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ∨ ") (fun fmt a -> f fmt a) )
         fmt disjuncts)
      fmt
      s.conjuncts


  let fol_of_cnf (convert_atom : A.t -> ('a, 'b) fol) (f: A.t cnf) : ('a, 'b) fol cnf =
      List.map (fun {disjuncts} ->
          List.map convert_atom disjuncts |> mk_disj
        ) f.conjuncts |> mk_conj
end


type tseitin_atom_t = {fol_id:string; generated:bool; is_neg:bool}

module TAtom() : TseitinAtomSig with type t = tseitin_atom_t = struct
  type t = tseitin_atom_t
  let pp fmt a = Format.(fprintf fmt "%s%s" 
      (if a.is_neg then "~" else "") a.fol_id)

  let gen = ref (-1)
  let fresh () = 
    gen := !gen + 1;
    Format.printf "called fresh! got %i@." !gen;
    {fol_id=(string_of_int !gen); generated=true; is_neg=false}
  let neg a = {a with is_neg=not a.is_neg}
  let get_atom_id a = a.fol_id
  let is_neg a = a.is_neg
  let is_generated a = a.generated

  let create fol_id = {fol_id; generated=false; is_neg=false}
end