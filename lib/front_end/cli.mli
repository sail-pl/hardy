(** {1 Command Line Interface} *)


type ltl_atom_t = Direct | PastLTL

exception IncorrectAtom
exception IncorrectAutFormat

val ltl_atom_t_of_string : string -> ltl_atom_t

val string_of_ltl_atom_t : ltl_atom_t -> string

type aut_format_t = Neverclaim | HOA

val aut_format_t_of_string : string -> aut_format_t

val string_of_aut_format_t : aut_format_t -> string

type info = {
    ltl_atom : ltl_atom_t;
    aut_format : aut_format_t;
    file : string;
    verbose : bool;
    outdir : string;
    no_i_a_conj : bool;
    smoke_tests : bool;
}
(** parameters provided by the cli *)

module type CliSig = sig val get_info : info end

(** Applicative functor because of side-effects inside *)
module Init : () -> CliSig
