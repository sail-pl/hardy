open HardyFrontEnd.Syntax
(* open HardyFrontEnd.Printer *)
open Program
open Shared
open HardyMisc.Utils

(** maintains a correspondance between an atom and its associated unique
    identifier *)
module type S = sig
  type 'a t

  type 'b data 

  val get_atom : string -> (string * ty fol_t) t
  (** [get_atom i] returns the short name and the atom corresponding to the identifier [i] *)

  val subst : string t -> string t
  (** [subst f ty_to_str] replaces each atoms in formula [f] by a
      printing-friendly string where the types inside the atoms are replaced by
      [f_ty_to_str] *)

  val add_and_get : ty fol_t -> (string * string) t
  (** [add_and_get a] returns the short and long identifier corresponding to the
      atom [a], creating a fresh one if it does not exist *)

  val get_data : string -> 'b data t
  val set_data : string -> 'b data -> unit t
end

(** [sub_atom_in_str subst s] matches all atoms inside string [s]. Each atom [a]
    is then replaced by [subst a] *)
let sub_atom_in_str subst =
  let open Str in
  let r = regexp {|f_\([0-9]+\)|} in
  global_substitute r (fun m -> matched_string m |> subst)

(** [atom_of_atom_id a] extracts the atom from the identifier [a]*)
let atom_of_atom_id s : int = 
    try String.(sub s 2 (length s - 2)) |> int_of_string with 
    | Failure _ | Invalid_argument _ -> failwith @@ Format.sprintf "couldn't extract atom '%s'" s

(** [remove_exp_loc e] replaces all locations of expression [e] with None *)
let rec remove_exp_loc (e : 't expr) : 't expr =
  let value =
    match e.value with
    | BinOp v ->
        let left = remove_exp_loc v.left and right = remove_exp_loc v.right in
        BinOp { v with left; right }
    | UnOp (ENot,e) -> UnOp (ENot,(remove_exp_loc e))
    | (Int _ | True | False | Var (_, _)) as v -> v
  in
  mk_dummy_loc value

(*
module Functional : S = struct
  module M = Map.Make (Int)

  type formula = string * ty fol_t
  (** string representing formula and the formula itself *)

  type 'a t = int * formula M.t -> 'a * (int * formula M.t)

  (* let return (x:'a) : 'a t = fun m -> (x,m)

  let bind (x : 'a t) (f : 'a -> 'b t) : 'b t =
   fun m ->
    let v,m = x m in
    f v m *)

  (* let get_f i proj : formula option t = fun m -> (M.find i (proj m), m) *)

  let get (s : string) : (string * ty fol_t) t =
   fun (cnt, m) -> (M.find (atom_of_atom_id s) m, (cnt, m))

  let subst (f : string t) : string t =
   fun m ->
    let f, (cnt, m) = f m in
    let get a : ty fol_t = get a (cnt, m) |> fst |> snd in
    ( sub_atom_in_str
        (fun s ->
          let a = get s in
          Format.(asprintf "%a" (pp_fol (pp_pred (pp_exp pp_hist)) pp_ty) a))
      f, (cnt, m) )

  (* let get_and_incr : int t = fun (cnt,m) -> cnt,(cnt+1,m) *)

  let add_and_get (atom : ty fol_t) : (string * string) t =
    let key = Hashtbl.hash (Format.asprintf "%a" (pp_fol (pp_pred (pp_exp pp_hist)) pp_ty) atom) in
    let label = Format.sprintf "f_%i" key in
    fun (cnt, m) ->
      match M.find_opt key m with
      | None ->
          let short_name = "F" ^ string_of_int cnt in
          let m' = M.add key (short_name, atom) m in
          ((short_name, label), (cnt + 1, m'))
      | Some (sn, _) -> ((sn, label), (cnt, m))
end
*)
module Imperative (Data: sig type t end) : S with type 'a t = 'a and type _ data = Data.t  = struct
  exception Atom_not_found of string

  open HardyFrontEnd.Printer

  type 'a t = 'a


  type _ data = Data.t (* forced to use a functor to know the type statically because of the value restriction *)

  type value = {short_id:string; fol:ty fol_t; other: Data.t option}

  (* we need to hash the key ourselves as we use them in the output *)
  module AtomTable = Hashtbl.Make(struct include Int let hash = Fun.id end)

  (* key is a hash of fol, value is a short name for fol + fol itself*)
  let atomic_bindings : value AtomTable.t = AtomTable.create 100
  let cnt = ref 0

  let get k : value =
    try AtomTable.find atomic_bindings (atom_of_atom_id k)
    with Not_found -> raise (Atom_not_found k)

  let get_atom (k : string) : (string * ty fol_t) t = let a = get k in (a.short_id, a.fol)

  let get_data k : Data.t t = (get k).other |> Option.get

  let set_data k (d:Data.t) = 
    let k = atom_of_atom_id k in 
    let a = AtomTable.find atomic_bindings k in AtomTable.replace atomic_bindings k {a with other=Some d}

  let subst =
    sub_atom_in_str (fun s ->
        Format.asprintf "%a" (pp_fol (pp_pred (pp_exp pp_hist)) pp_ty) (get s).fol)

  let add_and_get (atom : ty fol_t) =
    let key = Format.(asprintf "%a" (pp_fol (pp_pred (pp_exp pp_hist)) pp_ty) atom) |> String.hash in
    let label = Format.sprintf "f_%i" key in
    match AtomTable.find_opt atomic_bindings key with
    | None ->
        let short_id = string_of_int !cnt in
        AtomTable.add atomic_bindings key {short_id; fol=atom; other=None};
        incr cnt;
        (short_id, label)
    | Some a -> (a.short_id, label)
end
