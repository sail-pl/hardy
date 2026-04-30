(** The back-end requires:

    - generation of program declarations from the environment
    - generation of the initialization routine
    - generation of program specification
    - generation of a function's body
    - generation of a function from the body and its specification
    - generation of the program from the declarations, initialization procedure
      and functions *)
      
module type S =
  sig
    type local_spec
    type temp_spec
    type in_pgrm =
        (temp_spec, unit, local_spec, FrontParser.SharedSyntax.ty,
         FrontParser.SharedSyntax.ty FrontParser.ProgramSyntax.env)
        FrontParser.ProgramSyntax.program
    type in_setup =
        (local_spec, FrontParser.SharedSyntax.ty)
        FrontParser.ProgramSyntax.setup
    type in_body =
        (local_spec, FrontParser.SharedSyntax.ty)
        FrontParser.ProgramSyntax.stmt list
    type in_fun
    type in_spec
    type triple_data
    type out_pgrm
    type out_decl
    type out_body
    type out_setup
    type out_fun
    type processed_defs = {
      processed_decls : out_decl list;
      processed_setup : out_setup option;
      processed_functions : out_fun list;
    }
    val reset : unit -> unit
    val generate_declarations :
      FrontParser.SharedSyntax.ty FrontParser.ProgramSyntax.env ->
      out_decl list
    val generate_setup : in_setup -> out_setup
    val generate_body : in_body -> out_body
    val generate_function :
      ((in_spec, out_body) FrontParser.ProgramSyntax.hoare_triple,
       triple_data)
      HardyMisc.Utils.labeled -> out_fun
    val generate_program : processed_defs -> out_pgrm
    val write_program : string -> out_pgrm -> unit
  end



module F :
  (B : S) ->
    sig
      val translate_program :
        B.in_pgrm ->
        ((B.in_spec, B.in_fun) FrontParser.ProgramSyntax.hoare_triple,
         B.triple_data)
        HardyMisc.Utils.labeled HardyMisc.Utils.conjunction -> B.out_pgrm
      val write_program : string -> B.out_pgrm -> unit
    end
