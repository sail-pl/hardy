open HardyFrontEnd.Syntax.Program
open HardyFrontEnd.Printer
open HardyFrontEnd.Syntax.Fol

(** maintains a correspondance between an atom and its associated unique
    identifier *)
module type S = sig
  type 'a t

  val get : string -> (string * inst_spec_t) t
  (** [get i] returns the atom corresponding to the identifier [i] *)

  val subst : string t -> string t
  (** [subst f] replaces each atoms in formula [f] by a unique indentifier *)

  val add_and_get : inst_spec_t -> (string * string) t
  (** [add_and_get a] returns the short and long identifier corresponding to the
      atom [a], creating a fresh one if it does not exist *)
end

(** [sub_atom_in_str subst s] matches all atoms inside string [s]. Each atom [a]
    is then replaced by [subst a] *)
let sub_atom_in_str subst =
  let open Str in
  let r = regexp {|f_\([0-9]+\)|} in
  global_substitute r (fun m -> matched_string m |> subst)

(** [atom_id_to_int a] returns an integer representation of the atom identifier
    [a]*)
let atom_id_to_int s = String.(sub s 2 (length s - 2) |> int_of_string)

(** [remove_exp_loc e] replaces all locations of expression [e] with None *)
let rec remove_exp_loc (e : expr) : expr =
  let value =
    match e.value with
    | BinOp (e1, op, e2) ->
        let e1 = remove_exp_loc e1 and e2 = remove_exp_loc e2 in
        BinOp (e1, op, e2)
    | _ as x -> x
  in
  { value; loc = None }

(** [remove_fol_loc f] replaces all locations of fol formula [f] with None *)
let rec remove_fol_loc (f : expr fol) : expr fol =
  let value =
    match f.value with
    | Pred p -> Pred (remove_exp_loc p)
    | FOL_Unary (op, f) ->
        let f = remove_fol_loc f in
        FOL_Unary (op, f)
    | FOL_Binary (f1, op, f2) ->
        let f1 = remove_fol_loc f1 and f2 = remove_fol_loc f2 in
        FOL_Binary (f1, op, f2)
    | Forall (x, f) ->
        let f = remove_fol_loc f in
        Forall (x, f)
    | Exists (x, f) ->
        let f = remove_fol_loc f in
        Exists (x, f)
    | _ as x -> x
  in
  { value; loc = None }

module Functional : S = struct
  module M = Map.Make (Int)

  type formula = string * expr fol
  (** string representing formula and the formula itself *)

  type 'a t = int * formula M.t -> 'a * (int * formula M.t)

  (* let return (x:'a) : 'a t = fun m -> (x,m)

  let bind (x : 'a t) (f : 'a -> 'b t) : 'b t =
   fun m ->
    let v,m = x m in
    f v m *)

  (* let get_f i proj : formula option t = fun m -> (M.find i (proj m), m) *)

  let get (s : string) : (string * inst_spec_t) t =
   fun (cnt, m) -> (M.find (atom_id_to_int s) m, (cnt, m))

  let subst (f : string t) : string t =
   fun m ->
    let f, (cnt, m) = f m in
    let get a : inst_spec_t = get a (cnt, m) |> fst |> snd in
    ( sub_atom_in_str
        (fun s ->
          let a = get s in
          string_of_fol a)
        f,
      (cnt, m) )

  (* let get_and_incr : int t = fun (cnt,m) -> cnt,(cnt+1,m) *)

  let add_and_get (atom : inst_spec_t) : (string * string) t =
    let key = Hashtbl.hash (remove_fol_loc atom) in
    let label = Format.sprintf "f_%i" key in
    fun (cnt, m) ->
      match M.find_opt key m with
      | None ->
          let short_name = "F" ^ string_of_int cnt in
          let m' = M.add key (short_name, atom) m in
          ((short_name, label), (cnt + 1, m'))
      | Some (sn, _) -> ((sn, label), (cnt, m))
end

module Imperative () : S with type 'a t = 'a = struct
  exception Atom_not_found of string

  open HardyFrontEnd.Syntax.Fol
  open HardyFrontEnd.Printer

  type 'a t = 'a

  (* key is a hash of fol, value is a short name for fol + fol itself*)
  let atomic_bindings : (int, string * expr fol) Hashtbl.t = Hashtbl.create 100
  let cnt = ref 0

  let get (s : string) =
    try Hashtbl.find atomic_bindings (atom_id_to_int s)
    with Not_found -> raise (Atom_not_found s)

  let subst =
    sub_atom_in_str (fun s ->
        let _, inv = get s in
        string_of_fol inv)

  let add_and_get (atom : inst_spec_t) =
    (* we must get the same atom if the formulas are syntactically equal*)
    let key = Hashtbl.hash (remove_fol_loc atom) in
    let label = Format.sprintf "f_%i" key in
    match Hashtbl.find_opt atomic_bindings key with
    | None ->
        let short_name = "F" ^ string_of_int !cnt in
        Hashtbl.add atomic_bindings key (short_name, atom);
        incr cnt;
        (short_name, label)
    | Some (sn, _) -> (sn, label)
end
