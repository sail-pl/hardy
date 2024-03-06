(* open ArduinoSyntax.Locations *)
(* open ArduinoSyntax.Types *)
open ArduinoSyntax.Operators
open ArduinoSyntax.Fol
module S = ArduinoSyntax.Syntax
module AS = ArduinoSyntax.PromelaSyntax

open ArduinoSyntax.Locations
open ArduinoSyntax.Printer
open Why3
open S
module H = Ptree_helpers
module P = Ptree

(** Parameters for calling ltl2ba *)



(* Should be moved with the definition of bform ? *)
let fol_of_bform (convert_atom : string -> expr fol) =
  let open AS in
  let rec aux = function
    | True -> mk_dummy_loc FOL_True
    | False -> mk_dummy_loc FOL_False
    | Atom s -> convert_atom s
    | And (s1, s2) ->
        let s1 = aux s1 in
        let s2 = aux s2 in
        mk_dummy_loc (FOL_Binary (s1, And, s2))
    | Or (s1, s2) ->
        let s1 = aux s1 in
        let s2 = aux s2 in
        mk_dummy_loc (FOL_Binary (s1, Or, s2))
    | Not s ->
        let s = aux s in
        mk_dummy_loc (FOL_Unary (Not, s))
  in

  aux

  (* ok in file utils *)
(* Erase location to build a key *)
let rec determ_exp (e : expr) : expr =
  let value =
    match e.value with
    | BinOp (e1, op, e2) ->
        let e1 = determ_exp e1 and e2 = determ_exp e2 in
        BinOp (e1, op, e2)
    | _ as x -> x
  in
  { value; loc = None }

(* 2 formulas are equals if they are syntactically the same modulo their position *)
let rec determ_fol (f : expr fol) : expr fol =
  let value =
    match f.value with
    | Pred p -> Pred (determ_exp p)
    | FOL_Unary (op, f) ->
        let f = determ_fol f in
        FOL_Unary (op, f)
    | FOL_Binary (f1, op, f2) ->
        let f1 = determ_fol f1 and f2 = determ_fol f2 in
        FOL_Binary (f1, op, f2)
    | Forall (x, f) ->
        let f = determ_fol f in
        Forall (x, f)
    | Exists (x, f) ->
        let f = determ_fol f in
        Exists (x, f)
    | _ as x -> x
  in
  { value; loc = None }

module type AtomSig = sig
  val get : string -> string * expr fol
  val subst : string -> string
  val add : expr fol -> string * string
end

module Atom () : AtomSig = struct
  (* key is a hash of fol, value is a short name for fol + fol itself*)
  let atomic_bindings : (int, string * expr fol) Hashtbl.t = Hashtbl.create 100
  let cnt = ref 0

  let get (s : string) =
    let k = String.(sub s 2 (length s - 2) |> int_of_string) in
    Hashtbl.find atomic_bindings k

  let sub_atom_in_str f =
    let open Str in
    let r = regexp {|f_\([0-9]+\)|} in
    global_substitute r (fun m -> matched_string m |> f)

  let subst =
    sub_atom_in_str (fun s ->
        let _, inv = get s in
        string_of_fol inv)

  let add (f : expr fol) =
    let label = Format.sprintf "f_%i" in

    (* we must get the same atom if the formulas are syntactically equal*)
    let key = Hashtbl.hash (determ_fol f) in

    match Hashtbl.find_opt atomic_bindings key with
    | None ->
        let short_name = "F" ^ string_of_int !cnt in
        Hashtbl.add atomic_bindings key (short_name, f);
        incr cnt;
        (short_name, label key)
    | Some (sn, _) -> (sn, label key)
end
