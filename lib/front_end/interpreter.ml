open Syntax
open Shared
open Program
open HardyMisc.Utils


module M = struct
  exception TypingError of string

  (** a value can be nil, constant or a path to a value *)
  type value = 
  | Nil : value
  | LUnit : value
  | LInt : int -> value
  | LBool : bool -> value
  | LString : string -> value
  | LArray : value array -> value
  | Path : path -> value
  | LProd : value list -> value
  and path =
  | Var of string
  | ArrayCell of path * int 

  (** check if the value is empty *)
  let is_empty = function Nil -> true | _ -> false

  let rec pp_value fmt = function
    | Nil -> Format.fprintf fmt "nil"
    | LUnit -> Format.fprintf fmt "()"
    | LInt n -> Format.fprintf fmt "%i" n
    | LBool b -> Format.fprintf fmt "%b" b
    | LString s -> Format.fprintf fmt "%s" s
    | LArray l ->
        Format.(
          fprintf fmt "[%a]"
            (pp_print_array ~pp_sep:(fun fmt () -> fprintf fmt "; ") pp_value)
            l)
    | Path (Var s) -> Format.fprintf fmt "%s" s
    | Path (ArrayCell (id, n)) ->
        Format.fprintf fmt "%a[%i]" pp_value (Path id) n
    | LProd l -> Format.(fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pp_value) l)


  (** [get_int v] returns the integer associated to [v]
      @raise TypingError if v is not an int *)
  let get_int = function
    | LInt n -> n
    | v ->
        raise
          (TypingError
             (Format.asprintf "expected integer but got %a" pp_value v))

  (** [get_bool v] returns the boolean associated to [v] returns false if [v] is
      empty, and true if the value is neither a bool nor a path
      @raise TypingError if v is a path *)
  let get_bool = function
    | LBool b -> b
    | Nil -> false
    | LInt _ | LString _ | LArray _ | LProd _ -> true
    | Path _ | LUnit as v ->
        raise
          (TypingError (Format.asprintf "expected bool but got %a" pp_value v))

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
  | EAnd -> Bool2Bool (&&)
  | EOr -> Bool2Bool (||)

  let eval_bop op (x : value) (y : value) : value =
    match (get_bop_ty op, x, y) with
    | Int2Int f, LInt x, LInt y -> LInt (f x y)
    | Int2Bool f, LInt x, LInt y -> LBool (f x y)
    | Int2Bool _, Nil, LInt _ | Int2Bool _, LInt _, Nil -> Nil
    | Poly2Bool f, x, y -> LBool (f x y)
    | Bool2Bool f, _, _ -> LBool (f (get_bool x) (get_bool y))
    | _ -> raise (TypingError (Format.asprintf "%a %a %a" pp_value x Printer.pp_expr_binop op pp_value y))


  (*let read p id = 
    let l_ex cat_ty = Bindings.exists (fun s (cat_ty', _) -> s = id && cat_ty = cat_ty') p.prog_decls.env_variables in
    if l_ex State || l_ex Input then
      Hashtbl.find env id 
    else 
      if l_ex Output then
        raise (TypingError (Format.sprintf "attempted to read output '%s'" id))
      else 
        failwith @@ "unknown variable " ^ id

  let write p id upd = 
    let l_ex cat_ty = Bindings.exists (fun s (cat_ty', _) -> s = id && cat_ty = cat_ty') p.prog_decls.env_variables in
    if l_ex State || l_ex Output then
      Hashtbl.replace env id (upd (Hashtbl.find env id))
    else 
      if l_ex Input then
        raise (TypingError (Format.sprintf "attempted to write input '%s'" id))
      else 
        failwith @@ "unknown variable " ^ id
  
  *)

  let rec eval_rexpr p (e : _ expr) : value =
    match e.value with
    | Int x -> LInt x
    | True -> LBool true
    | False -> LBool false
    | Unit -> LUnit
    | String s -> LString s
    | Array l -> LArray (Array.of_list (List.map (eval_rexpr p) l))
    | Var (id, _) -> read p id
    | ArrayCell v -> (
        let id = eval_rexpr p v.array in
        match id with
        | LArray l -> l.(get_int (eval_rexpr p v.idx))
        | _ -> failwith @@ "rexpr: not an array")
    | UnOp (ENot,e) -> LBool (get_bool (eval_rexpr p e) |> not)
    | BinOp v ->
        let e1 = eval_rexpr p v.left in
        let e2 = eval_rexpr p v.right in
        eval_bop v.op e1 e2
    | Prod l -> LProd (List.map (eval_rexpr p) l)
    | NodeCall _ ->  failwith "todo node call"

  and eval_lexpr p (e : _ expr) : path =
    match e.value with
    | Var (id, _) -> Var id
    | ArrayCell v ->
        let id = eval_lexpr p v.array in
        ArrayCell (id, get_int (eval_rexpr p v.idx))
    | _ -> failwith "not an l-value"
  
  let rec update_path pgrm upd = function
    | Var s ->
        if Bindings.mem s pgrm.prog_decls.env_variables then
          try
            Hashtbl.(
              let x = find env s in
              replace env s (upd x))
          with Not_found -> failwith @@ "couldn't find " ^ s
        else failwith @@ "[update_path] unknown variable " ^ s
    | ArrayCell (path, n) ->
        update_path pgrm
          (function
            | LArray l ->
                l.(n) <- upd l.(n);
                LArray l
            | _ -> failwith "not an array")
          path

  let eval_stmts p (s : _ stmt list) : unit =
    let eval_rexpr = eval_rexpr p in
    let eval_lexpr = eval_lexpr p in
    let rec eval_stmt (s : _ stmt) =
      match s.value with
      | Return e ->
        let _e = eval_rexpr e in
        failwith "todo return"
      | Assign (e1, e2) ->
          let e1 = eval_lexpr e1 in
          let e2 = eval_rexpr e2 in
          update_path p (fun _ -> e2) e1
      | If (cond, s_true, s_false) ->
          if get_bool (eval_rexpr cond) then eval_seq s_true
          else Option.iter eval_seq s_false
      | While (cond, _, _, s') ->
          if get_bool (eval_rexpr cond) then (
            eval_seq s';
            eval_stmt s)
          else ()
    and eval_seq (stmts : _ stmt list) : unit = List.iter eval_stmt stmts in
    eval_seq s
end


module type IOBridgeSig = sig
  val get_inputs : string -> base_ty var_decls -> unit

  val send_outputs : string -> base_ty var_decls -> unit
end

let eval_pgrm (p: base_program) (module B : IOBridgeSig) = 
  let open M in
  Bindings.iter (fun v (cat,_) -> match cat with Input | State | Output -> Hashtbl.add env v Nil | _ -> ()) p.prog_decls.env_variables;

    let rec exec_transition p eval = function
    | [] -> None
    | (None,s,next)::_ -> eval p s; next
    | (Some guard, s, next) :: t ->
        if get_bool (eval_rexpr p guard) then
          (eval p s; next)
        else exec_transition p eval t
  in

  let rec run (n: _ node) : unit =  

    (* collect new inputs *)
    B.get_inputs n.node_id (
      Bindings.to_seq p.prog_decls.env_variables 
      |> Seq.filter_map (fun (s,(cat_ty,ty)) -> if cat_ty = Input then Some (s,ty) else None) 
      |> List.of_seq 
    );
    (* reset all outputs *)
    Bindings.iter (fun v (cat, _) -> if cat = Output then Hashtbl.add env v Nil) p.prog_decls.env_variables;

    (* open new scope with local variables *)
    List.iter (fun (v, _) -> Hashtbl.add env v Nil) n.node_variables;
    let local_p =
      let env_variables = Bindings.(merge (fun _ _ v2 -> v2) (of_list n.node_variables) p.prog_decls.env_variables) in
      {
        p with
        prog_decls =
          {
            env_variables;
          };
      }
    in

    (* evaluate preamble code if it exists *)
    eval_stmts local_p n.node_preamble;

    (* evaluate code in first matching transition, top to bottom *)    
    let next = exec_transition local_p eval_stmts n.node_transitions in

    (* send new outputs (sync mode)
      todo: async mode where external program can request anytime the output
    *)
    B.send_outputs n.node_id (
      Bindings.to_seq p.prog_decls.env_variables 
      |> Seq.filter_map (fun (s,(cat_ty,ty)) -> if cat_ty = Output then Some (s,ty) else None) 
      |> List.of_seq 
    );
    (* remove scope *)
    List.iter (fun (v, _) -> Hashtbl.remove env v) n.node_variables;

    (* get the next node *)
    let next_node = 
      Option.fold next 
        ~none:n 
        ~some:(fun n -> try find_node p.prog_nodes n with Not_found -> failwith @@ Format.sprintf "no such node '%s'"  n) 
    in

    (* go to the next node *)
    run next_node
  in
  run (find_start_node p.prog_nodes)


module ConsoleBridge : IOBridgeSig = struct
  open M

  let get_inputs state i = 
    let rec get_input (i,t) : value = 
      let get f = 
        Format.printf "%s? " i;  Format.print_flush ();
        let v = try read_line () with End_of_file -> exit 0 in
        if v = "" then Nil else f v
      in
      match t with
      | Ty_String -> get (fun s -> LString s)
      | Ty_Bool -> get (fun i -> LBool (bool_of_string i))
      | Ty_Int -> get (fun i -> LInt (int_of_string i))
      | Ty_Array (ty, n) ->
          let arr = Array.make n Nil in
          for cnt = 1 to n do
            let msg = Format.sprintf "%s(%i/%i)" i cnt n in
            arr.(cnt - 1) <- get_input (msg, ty)
          done;
          LArray arr
      | Ty_Prod [] -> get (fun _ -> LProd [])
      | Ty_Prod l -> 
        let n = List.length l in 
        let _,p = 
        List.fold_left (fun (cnt,l) ty-> 
          let msg = Format.sprintf "%s(%i/%i)" i cnt n in
          let v =  get_input (msg, ty) in
         (cnt+1,v::l)) (1,[]) l
        in LProd (List.rev p)

    in
    Format.printf "=== INPUTS (%s) ===@." state;
    List.iter (fun (i,t) -> Hashtbl.replace env i (get_input (i,t))) i

  let send_outputs state o = 
    Format.printf "=== OUTPUTS (%s) ===@." state;
    List.iter (fun (o, _) ->
        Format.printf "%s: %a@." o
          (fun fmt -> pp_value fmt)
          (Hashtbl.find env o)) o
end