type w3 = {
  config : Why3.Whyconf.config;
  main : Why3.Whyconf.main;
  env : Why3.Env.env;
}

val init_why3 : unit -> w3
val print_program : Why3.Ptree.mlw_file -> string -> unit
val get_alt_ergo : w3 -> Why3.Whyconf.config_prover * Why3.Driver.driver
val get_loc : (Lexing.position * Lexing.position) option -> Why3.Loc.position
val why3_and : Why3.Ptree.term -> Why3.Ptree.term -> Why3.Ptree.term
val why3_or : Why3.Ptree.term -> Why3.Ptree.term -> Why3.Ptree.term
val unit_val : Why3.Ptree.expr_desc
