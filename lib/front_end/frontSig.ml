open Syntax
open Shared

type temp_f_prop = {
    mentions_input: bool;
    mentions_output: bool;
    mentions_state: bool;
    mentions_history: bool;
}
let is_static_prop p = not (p.mentions_input || p.mentions_output || p.mentions_state)

let dft_temp_f_prop = {mentions_input=false; mentions_output=false; mentions_state=false; mentions_history=false} 


let mentions_temp_f_prop (c:cat_ty) : temp_f_prop = match c with 
  | State -> {dft_temp_f_prop with mentions_state=true}
  | Input -> {dft_temp_f_prop with mentions_input=true}
  | Output -> {dft_temp_f_prop with mentions_output=true}
  | Local -> dft_temp_f_prop

let join_temp_f_prop p1 p2 = 
  let mentions_input = p1.mentions_input || p2.mentions_input 
  and mentions_output = p1.mentions_output || p2.mentions_output
  and mentions_state = p1.mentions_state || p2.mentions_state
  and mentions_history = p1.mentions_history || p2.mentions_history
  in
  {mentions_input ; mentions_output; mentions_state; mentions_history}


module type Typing = sig
    type in_local_spec
    type in_temp_spec
    type out_local_spec
    type out_temp_spec


    val type_pgrm : 
        (
          in_temp_spec, 
          unit, 
          in_local_spec, 
          unit, 
          ProgramSyntax.parsed_env
        ) 
        Program.program -> 
                  
        (
          out_temp_spec,
          unit, 
          out_local_spec, 
          Shared.ty, 
          Shared.ty ProgramSyntax.env
        ) Program.program
end

