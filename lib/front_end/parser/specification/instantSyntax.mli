(** Evolution of a variable value across instants. The initial instant is [At 0]
    and last instant is [Previous 1]. The current instant is [Previous 0]
    Negative values have no semantics *)
type instant = At of int | Previous of int

(** approximation of the number of instants *)
type min_nb_instants = { nb_instant : int; is_max : bool; }

val pp_min_nb_instant : Format.formatter -> min_nb_instants -> unit

val min_nb_instant_dft : min_nb_instants

val add_nb_instant : int -> min_nb_instants -> min_nb_instants

val make_exactly : min_nb_instants -> min_nb_instants

val join_nb_instant : min_nb_instants list -> min_nb_instants
