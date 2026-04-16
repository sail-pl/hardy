open HardyFrontEnd
open HardyMisc.Utils


module type TseitinAtomSig = sig
  include Msat_tseitin.Arg

  val create : string -> t
  val get_atom_id : t -> string

  val is_neg : t -> bool
  val is_generated : t -> bool
end

module Tseintin(A : TseitinAtomSig) = struct
  open Syntax.Shared
  include Msat_tseitin.Make(A)
  
  let rec to_tseitin : 'a bool_a -> t = 
    function      
    | True -> f_true
    | False -> f_false
    | And (f1,f2) -> make_and [to_tseitin f1; to_tseitin f2]
    | Or (f1,f2) -> make_or [to_tseitin f1; to_tseitin f2]
    | Atom a -> make_atom a
    | Not f -> make_not (to_tseitin f)
    

  let to_cnf (f : 'a bool_a) : A.t cnf  = 
    (make_cnf (to_tseitin f) |> List.map mk_disj) |> mk_conj
end

type tseitin_atom_t = {fol_id:string; generated:bool; is_neg:bool}

(** imperative version *)
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