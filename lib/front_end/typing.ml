open FrontParser.Program
open HardyMisc.Utils
open Syntax.Shared

(* todo: move some backend analysis here *)
let type_pgrm (p : parsed_program) : base_program = 
    (* todo: check empty intersection of inputs/outputs/variables *)
    let bindings = 
        (List.to_seq p.prog_decls.env_input |> Seq.map (fun (s,t) -> (s,(Input, t)))) |> Seq.append
        (List.to_seq p.prog_decls.env_output |> Seq.map (fun (s,t) -> (s,(Output, t)))) |> Seq.append
        (List.to_seq p.prog_decls.env_variables |> Seq.map (fun (s,t) -> (s,(State, t)))) |> Bindings.of_seq 
    in
    { p with prog_decls={env_variables=bindings}}

