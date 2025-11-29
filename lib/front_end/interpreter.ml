open Syntax
open Shared
open Program
open HardyMisc.Utils

type value = 
| Int : int -> value
| Bool : bool -> value

let get_int =  function Int n -> n | _ -> failwith "expected int"
let get_bool = function Bool b -> b | _ -> failwith "expected bool"


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
| Gt -> Poly2Bool (<)
| Lt -> Poly2Bool (>)
| Gte -> Poly2Bool (>=)
| Lte -> Poly2Bool (<=)
| Eq -> Poly2Bool (=)
| Neq -> Poly2Bool (<>)
| EAnd -> Bool2Bool (&&)
| EOr -> Bool2Bool (||)

let eval_bop op (x: value) (y: value) : value = 
  match get_bop_ty op,x,y with
  | Int2Int f, Int x, Int y -> Int (f x y)
  | Int2Bool f, Int x, Int y -> Bool (f x y)
  | Poly2Bool f, x, y -> Bool (f x y)
  | Bool2Bool f, Bool x, Bool y -> Bool (f x y)
  | _ -> failwith "typing error"

let eval_expr p (e: _ expr) : value = 
  let rec aux (e: _ expr) = match e.value with
  | Int x -> Int x
  | True -> Bool true
  | False -> Bool false
  | Var (id, _) ->
    if Bindings.mem id p.prog_decls.env_variables
  then 
    try Hashtbl.find env id with _ -> failwith @@ "unknown input/variable " ^ id
    else  failwith @@ "unknown variable " ^ id
  | UnOp (ENot, e) -> Bool (get_bool (aux e) |> not)
  | BinOp be -> 
    let left = aux be.left 
    and right = aux be.right in
    eval_bop be.op left right
in aux e

let eval_stmts p (s: _ stmt list) : unit =  
  let eval_expr = eval_expr p in
  let rec eval_stmt (s: _ stmt) = 
    match s.value with
  | Assign (_left, _right) -> failwith "todo"
  | Emit (e, id) -> 
    if Bindings.exists (fun s (ct,_) -> s=id && ct = Input) p.prog_decls.env_variables then 
      Hashtbl.replace env id (eval_expr e) 
    else failwith @@ "unknown output " ^ id
  | If (cond, s_true, s_false) -> if (get_bool (eval_expr cond)) then eval_seq s_true else 
    Option.iter eval_seq s_false
  | While (cond, _, _, s') -> 
    if get_bool (eval_expr cond) then  (eval_seq s'; eval_stmt s) else ()
  and eval_seq (stmts: _ stmt list) : unit = List.iter eval_stmt stmts
  in eval_seq s



module type IOBridgeSig = sig
  val get_inputs : base_ty var_decls -> unit

  val send_outputs : base_ty var_decls -> unit
end


module ConsoleBridge : IOBridgeSig = struct
  let get_inputs i = List.iter (fun (i,t) -> 
    Printf.printf "value for %s? " i;
    let v = read_line () in
    let v = match t with
    | Ty_Bool -> Bool (bool_of_string v)
    | Ty_Int -> Int (int_of_string v)
    in
    Hashtbl.replace env i v
  ) i

  let send_outputs o = List.iter (fun (o,_) ->
    match Hashtbl.find_opt env o with
    | Some (Bool true) -> Printf.printf "%s: true\n" o
    | Some (Bool false) -> Printf.printf "%s: false\n" o
    | Some (Int v) -> Printf.printf "%s: %i\n" o v
    | None -> Printf.printf "%s: absent\n" o

  ) o
end


let eval_pgrm (p: base_program) (module B : IOBridgeSig) = 
  let rec run (n: _ node) =  
    let rec do_transition = function
    | [] -> run n
    | (None,new_node)::_ -> run (find_node new_node p.prog_nodes)
    | (Some guard,new_node)::t ->
      if get_bool (eval_expr p guard) then 
        run (find_node new_node p.prog_nodes)
      else
        do_transition t
    in


    (* open new scope with local variables *)
    (* n.node_variables *)

    eval_stmts p n.node_body;
    
    B.send_outputs (
      Bindings.to_seq p.prog_decls.env_variables 
      |> Seq.filter_map (fun (s,(cat_ty,ty)) -> if cat_ty = Output then Some (s,ty) else None) 
      |> List.of_seq 
    );

    Unix.sleep 1;
    flush_all ();

    B.get_inputs (
      Bindings.to_seq p.prog_decls.env_variables 
      |> Seq.filter_map (fun (s,(cat_ty,ty)) -> if cat_ty = Input then Some (s,ty) else None) 
      |> List.of_seq 
    );

    do_transition n.node_transitions
  in  
  let start = find_start_node p.prog_nodes in
  run start
  