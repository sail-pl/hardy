open Syntax
open Shared
open Program
open HardyMisc.Utils

type value = 
| LEmpty : value
| LInt : int -> value
| LBool : bool -> value
| LString : string -> value
| LArray : value array -> value
| Path : path -> value
and path =
| Var of string
| ArrayCell of path * int 



let rec pp_value fmt = function 
  | LEmpty -> Format.fprintf fmt "nil"
  | LInt n -> Format.fprintf fmt "%i" n
  | LBool b -> Format.fprintf fmt "%b" b
  | LString s -> Format.fprintf fmt "%s" s
  | LArray l -> Format.(fprintf fmt "[%a]" (pp_print_array ~pp_sep:(fun fmt () -> fprintf fmt "; ") pp_value) l)
  | Path Var s -> Format.fprintf fmt "%s" s
  | Path ArrayCell (id,n)  -> Format.fprintf fmt "%a[%i]" pp_value (Path id) n


let get_int =  function LInt n -> n | _ -> failwith "expected int"
let get_bool = function LBool b -> b | LEmpty -> false | LInt _ -> true | _ -> failwith "expected bool"


let env : (string, value) Hashtbl.t = Hashtbl.create 20


type bop_ty = 
  | Int2Int : (int -> int -> int) -> bop_ty
  | Bool2Bool : (bool -> bool -> bool) -> bop_ty
  | Int2Bool : (int -> int -> bool) -> bop_ty
  | Poly2Bool : (value -> value -> bool) -> bop_ty

let get_bop_ty = function
| Add -> Int2Int (+)
| Sub -> Int2Int (-)
| Mul -> Int2Int ( * )
| Div -> Int2Int (/)
| Gt -> Int2Bool (>)
| Lt -> Int2Bool (<)
| Gte -> Int2Bool (>=)
| Lte -> Int2Bool (<=)
| Eq -> Poly2Bool (=)
| Neq -> Poly2Bool (<>)
| And -> Bool2Bool (&&)
| Or -> Bool2Bool (||)

let eval_bop op (x: value) (y: value) : value = 
  match get_bop_ty op,x,y with
  | Int2Int f, LInt x, LInt y -> LInt (f x y)
  | Int2Bool f, LInt x, LInt y ->LBool (f x y)
  | Int2Bool _, LEmpty, LInt _ | Int2Bool _, LInt _,LEmpty -> LEmpty
  | Poly2Bool f, x, y -> LBool (f x y)
  | Bool2Bool f, _,_-> LBool (f (get_bool x) (get_bool y))
  | _ -> failwith "typing error"


let do_if_var_exists p f id = 
  if 
  List.exists (fun (o,_) -> o=id) p.prog_decls.env_variables 
  || 
  List.exists (fun (o,_) -> o=id) p.prog_decls.env_input
  ||
  List.exists (fun (o,_) -> o=id) p.prog_decls.env_output
  then f ()
else failwith @@ "[do_if_var_exists] unknown variable " ^ id
  


let rec eval_rexpr p (e: _ expr) : value = 
  let rec aux (e: _ expr) = match e.value with
  | Int x -> LInt x
  | True -> LBool true
  | False -> LBool false
  | String s -> LString s
  | Array l -> LArray (Array.of_list (List.map aux l))
  | Var (id, _) | Read id ->
    do_if_var_exists p (fun () -> try Hashtbl.find env id with _ -> failwith @@ "unknown input/variable " ^ id) id
  | ArrayCell (id,n) -> 
    let id = eval_rexpr p id in 
    (
      match id with
      | LArray l -> l.(get_int (aux n))
      |  _ -> failwith @@ "rexpr: not an array"
    )
  | Not e -> LBool (get_bool (aux e) |> not)
  | BinOp (e1, op, e2) -> 
    let e1 = aux e1 in
    let e2 = aux e2 in
    eval_bop op e1 e2
in aux e
and eval_lexpr p (e: _ expr) : path = 
  let aux (e: _ expr) = match e.value with
  | Var (id, _) | Read id -> Var id
  | ArrayCell (id,idx) -> let id = eval_lexpr p id in ArrayCell (id,get_int (eval_rexpr p idx))
  | _ -> failwith "not an l-value"
in aux e


let rec update_path pgrm upd = function
| Var s ->  
  if List.exists (fun (v,_) -> v=s) pgrm.prog_decls.env_variables then 
    try Hashtbl.(let x = find env s in replace env s (upd x)) with Not_found -> failwith @@ "couldn't find " ^ s
  else failwith @@ "[update_path] unknown variable " ^ s

| ArrayCell (path,n) -> 
  update_path pgrm (function LArray l -> l.(n) <- (upd l.(n)); LArray l | _ -> failwith "not an array")  path

let eval_stmts p (s: _ stmt list) : unit =  
  let eval_rexpr = eval_rexpr p in
  let eval_lexpr = eval_lexpr p in
  let rec eval_stmt (s: _ stmt) = 
    match s.value with
  | Assign (e1, e2) ->
    let e1 = eval_lexpr e1 in
    let e2 = eval_rexpr e2 in
    update_path p (fun _ -> e2) e1
  | Clear e -> update_path p (fun _ -> LEmpty) (eval_lexpr e) 
  | Emit (e, id) -> 
    let e = Option.(map eval_rexpr e |> value ~default:LEmpty) in
    if List.exists (fun (o,_) -> o=id) p.prog_decls.env_output then 
      Hashtbl.replace env id e 
    else failwith @@ "unknown output " ^ id
  | If (cond, s_true, s_false) -> if (get_bool (eval_rexpr cond)) then eval_seq s_true else 
    Option.iter eval_seq s_false
  | While (cond, _, _, s') -> 
    if get_bool (eval_rexpr cond) then  (eval_seq s'; eval_stmt s) else ()

  and eval_seq (stmts: _ stmt list) : unit = List.iter eval_stmt stmts
  in eval_seq s



module type IOBridgeSig = sig
  val get_inputs : string -> base_ty var_decls -> unit

  val send_outputs : string -> base_ty var_decls -> unit
end


module ConsoleBridge : IOBridgeSig = struct
  let get_inputs state i = 
    let rec get_input (i,t) : value = 
      let get f = 
        Format.printf "%s? " i;  Format.print_flush ();
        let v = try read_line () with End_of_file -> exit 0 in
        if v = "" then LEmpty else f v
      in
      match t with
      | Ty_String -> get (fun s -> LString s)
      | Ty_Bool -> get (fun i -> LBool (bool_of_string i))
      | Ty_Int -> get (fun i -> LInt (int_of_string i))
      | Ty_Array (ty,n) -> 
        let arr = Array.make n LEmpty in
        for cnt = 1 to n do 
          let msg = Format.sprintf "%s(%i/%i)" i cnt n in
          arr.(cnt-1) <- get_input (msg,ty)
        done; LArray arr

    in
    Format.printf "=== INPUTS (%s) ===@." state;
    List.iter (fun (i,t) -> Hashtbl.replace env i (get_input (i,t))) i

  let send_outputs state o = 
    Format.printf "=== OUTPUTS (%s) ===@." state;
    List.iter (fun (o,_) ->
    match Hashtbl.find_opt env o with
    | Some v -> Format.printf "%s: %a@." o (fun fmt -> pp_value fmt) v
    | None -> Format.printf "%s: absent@." o
  ) o ;

end


let eval_pgrm (p: base_program) (module B : IOBridgeSig) = 
  List.iter (fun (v,_) -> Hashtbl.add env v LEmpty) p.prog_decls.env_variables;
  List.iter (fun (v,_) -> Hashtbl.add env v LEmpty) p.prog_decls.env_input;


  let rec run (n: _ node) : unit =  
    let rec do_transition p cleanup t = 
      let cleanup_and_find_node = function
        | Some n -> (cleanup (); try run (find_node n p.prog_nodes) with Not_found -> failwith @@ "unknown node " ^ n )
        | None -> cleanup (); run n
      in
      match t with
      | [] -> cleanup_and_find_node None
      | (None,new_node)::_ -> cleanup_and_find_node (Some new_node)
      | (Some guard,new_node)::t ->
        if get_bool (eval_rexpr p guard) then 
          cleanup_and_find_node (Some new_node)
        else
          do_transition p cleanup t
    in

    (* open new scope with local variables *)
    List.iter (fun (v,_) -> Hashtbl.add env v LEmpty) n.node_variables;
    let local_p = {p with prog_decls = {p.prog_decls with env_variables = n.node_variables@p.prog_decls.env_variables }} in


    B.get_inputs n.node_id p.prog_decls.env_input;
    eval_stmts local_p n.node_body ;
    B.send_outputs n.node_id p.prog_decls.env_output ;

    (* remove scope *)
    let cleanup () = List.iter (fun (v,_) -> Hashtbl.remove env v) n.node_variables in

    (* go to the next state after removing local scope *)
    do_transition local_p cleanup n.node_transitions 
  in  
  run (find_start_node p.prog_nodes)
  