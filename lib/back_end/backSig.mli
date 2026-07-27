(** {1 Back-end signature} *)
      
open FrontParser.SharedSyntax

module type S =
  sig
    type local_spec
    type temp_spec

    include HardyMisc.Utils.PIPELINE

    type in_fun
    type in_spec
    type triple_data
    val reset : unit -> unit
    val translate_program : in_t -> ((in_spec,in_fun) hoare_triple, triple_data) HardyMisc.Utils.labeled HardyMisc.Utils.conjunction -> out_t
    val write_program : string -> out_t -> unit
  end