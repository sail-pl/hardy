(** {1 Specification } *)

(** data of first-order logic formulas *)
type 'a formula_data = {formula_data : 'a}

(** *)
type 'a triple_data = {triple_data : 'a}


(** data of the conjunction of formulas *)
type 'a cnf_data = {cnf_data : 'a}


(** data of the product automaton transitions *)
type 'a transition_data = {transition_data : 'a}


module type T = sig
    type ('ty,'qty) fol_t

    type ('ty, 'qty, 'data) inst_spec_t
    (** instantaneous specification of program expression *)

    type ('atom_label,'ty,'qty) temp_spec_t
    (** ltl logic with fol over program expression where variables can be temporally
        quantified *)


    type parsed_temp_spec_t
    type parsed_spec_t
    type base_spec_t

    type cnf_data
    type triple_data
    type formula_data
    type transition_data
end