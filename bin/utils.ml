open Why3

type w3 = {config : Whyconf.config; main :Whyconf.main; env : Env.env}


let init_why3 () : w3 = 
  let open Whyconf in 
  let config = init_config None in
  let main =get_main config in
  let env = loadpath main |> Env.create_env in
  {config;main;env}



  let get_input_file () = 
    if Array.length Sys.argv <> 2 then  begin
      Printf.printf "Usage: %s <filename>\n" Sys.argv.(0);
      exit 1
    end
    else Sys.argv.(1)
  

let print_program p =  
  p 
  |> Fun.flip (Mlw_printer.pp_mlw_file ~attr:true)
  |> Pp.print_in_file 


let print_annotated_program (loc,e) p = 
  let msg = Format.asprintf "%a" Exn_printer.exn_printer e in
  p
  |> Fun.flip (Mlw_printer.with_marker ~msg loc Mlw_printer.pp_mlw_file)
  |> Pp.print_in_file 

(* let get_fol_theory =  Pmodule.read_module "" *)