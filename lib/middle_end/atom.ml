open HardyFrontEnd.Syntax
open Program
(* open HardyFrontEnd.Printer *)
(* open Shared *)
open HardyMisc.Utils

(** maintains a correspondance between an atom and its associated unique
    identifier *)
module type S = sig
  include MONADIC

  type data 
  type atom 

  val get_atom : string t -> (string * atom) t
  (** [get_atom i] returns the short name and the atom corresponding to the identifier [i] *)

  val subst : string t -> string t
  (** [subst f ty_to_str] replaces each atoms in formula [f] by a
      printing-friendly string where the types inside the atoms are replaced by
      [f_ty_to_str] *)

  val register_atom : atom t -> (string * string) t
  (** [register_atom a] returns the short and long identifier corresponding to the
      atom [a], creating fresh ones if they do not exist  *)

  val get_atom_ids : atom t -> (string * string) t
  (** [get_atom_ids a] returns the short and long identifier corresponding to the
      atom [a], that is required to have been previously registered *)

  val get_data : string -> data t
  val set_data : string -> data -> unit t

end

(** [sub_atom_in_str subst s] matches all atoms inside string [s]. Each atom [a]
    is then replaced by [subst a] *)
let sub_atom_in_str subst =
  let open Str in
  let r = regexp {|p\([0-9]+\)|} in
  global_substitute r (fun m -> matched_string m |> subst)

(** [atom_of_atom_id a] extracts the atom from the identifier [a]*)
let atom_of_atom_id s : int = 
    try int_of_string s with 
    | Failure _ -> 
      try String.(sub s 1 (length s - 1)) |> int_of_string with 
      | Invalid_argument err | Failure err -> failwith @@ Format.sprintf "%s (couldn't extract atom '%s')" err s


(** [remove_exp_loc e] replaces all locations of expression [e] with None *)
let rec remove_exp_loc (e : 't expr) : 't expr =
  let value =
    match e.value with
    | BinOp v ->
        let left = remove_exp_loc v.left and right = remove_exp_loc v.right in
        BinOp { v with left; right }
    | UnOp (ENot,e) -> UnOp (ENot,(remove_exp_loc e))
    | (Int _ | Real _ | True | False | Var (_, _)) | String _ as v -> v
    | ArrayCell v -> 
      let idx = remove_exp_loc v.idx 
      and array = remove_exp_loc v.array in
      ArrayCell {idx;array}
    | Array l -> Array (Iarray.map remove_exp_loc l)
    | Prod l -> Prod (List.map remove_exp_loc l)
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
    let label = Format.sprintf "p_%i" key in
    fun (cnt, m) ->
      match M.find_opt key m with
      | None ->
          let short_name = "P" ^ string_of_int cnt in
          let m' = M.add key (short_name, atom) m in
          ((short_name, label), (cnt + 1, m'))
      | Some (sn, _) -> ((sn, label), (cnt, m))
end
*)


module Imperative (Data: SIMP_TYPE) (Atom: PRETTY_SIMP_TYPE (* atom type *)) : S with type atom = Atom.t with 
  type 'a t = 'a and
  type data = Data.t and
  type atom = Atom.t
  = struct
  exception Atom_not_found of string

  type 'a t = 'a


  (* forced to use a functor to know the type statically because of the value restriction *)

  type data = Data.t
  
  type atom = Atom.t


  type 'a value = {short_id:string; atom: atom; other: 'a option}

  (* we need to hash the key ourselves as we use them in the output *)
  module AtomTable = Hashtbl.Make(struct include Int let hash = Fun.id end)

  let map f x = f x

  let join = Fun.id

  (* key is a hash of fol, value is a short name for fol + fol itself*)
  let atomic_bindings : 'a value AtomTable.t = AtomTable.create 100
  let cnt = ref 0

  let get k : 'a value =
    try AtomTable.find atomic_bindings (atom_of_atom_id k)
    with Not_found -> 
      AtomTable.iter (fun k v -> Format.printf "%i -> %a @." k Atom.pp v.atom) atomic_bindings;
      raise (Atom_not_found k)

  let get_atom (k : string) : (string * atom) t = let a = get k in (a.short_id, a.atom)

  let get_data k : 'a t = (get k).other |> Option.get

  let set_data k (d: 'a) = 
    let k = atom_of_atom_id k in 
    let a = AtomTable.find atomic_bindings k in AtomTable.replace atomic_bindings k {a with other=Some d}

  let subst =
    sub_atom_in_str (fun s ->
        Format.(asprintf "%a" Atom.pp (get s).atom))

  let get_atom_ids atom = 
    let key = Format.(asprintf "%a" Atom.pp atom) |> String.hash in
    let label = Format.sprintf "p%i" key in
    let a = AtomTable.find atomic_bindings key in
    (a.short_id,label)

  let register_atom (atom : atom) =
    let key = Format.(asprintf "%a" Atom.pp atom) |> String.hash in
    let label = Format.sprintf "p%i" key in
    match AtomTable.find_opt atomic_bindings key with
    | None ->
        (* Format.printf "adding atom %s@." label; *)
        let short_id = string_of_int !cnt in
        AtomTable.add atomic_bindings key {short_id; atom; other=None};
        incr cnt;
        (short_id, label)
    | Some a -> (a.short_id, label)
end
