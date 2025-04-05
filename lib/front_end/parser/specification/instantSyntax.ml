(** Evolution of a variable value across instants. The initial instant is [At 0]
    and last instant is [Previous 1]. The current instant is [Previous 0]
    Negative values have no semantics *)
type instant = At of int | Previous of int

type min_nb_instants = { nb_instant : int; is_max : bool }
(** approximation of the number of instants *)

let min_nb_instant_dft = { nb_instant = 0; is_max = false }
let add_nb_instant n i = { i with nb_instant = i.nb_instant + n }
let make_exactly i = { i with is_max = true }

let join_nb_instant : min_nb_instants list -> min_nb_instants =
  HardyMisc.Utils.fold_mjoin Fun.id
    (fun (i : min_nb_instants) (acc : min_nb_instants) ->
      if i.is_max && acc.is_max && i.nb_instant = acc.nb_instant then acc
      else
        let nb_instant = min i.nb_instant acc.nb_instant in
        { nb_instant; is_max = false })
    { is_max = true; nb_instant = 0 }

(* type 'a tquant =
| All of * 'a
| Any of * 'a
|  *)

(* [All] and [Any] are universal and existential quantifiers over an history range, bounds included *)

(** go back to the previous instant, returns None if no such instant exists *)
(* let prev = function
| Current -> Some (At (-1))
| At n -> if n > 0 then At (n-1) else None *)
