open HardyFrontEnd
open Syntax
open Shared
open Fol
open Printer
open Why3
open Utils
open HardyMisc.Utils
open Program


module PH = Ptree_helpers
module P = Ptree

let get_pp_string a b = Format.asprintf "%a" a b

let get_cat_ty = get_pp_string (pp_private pp_cat_ty) 

let get_custom_pty ty = Ptree.(PTtyapp (Ptree_helpers.qualid [ty ], []))

let rec get_pty  = function
| Ty_Bool 
| Ty_String
| Ty_Int
| Ty_Real as ty -> Ptree.(PTtyapp (Ptree_helpers.qualid [ get_pp_string pp_base_ty ty ], []))
| Ty_Array (ty',_) -> Ptree.(PTtyapp (Ptree_helpers.qualid [ "array" ], [get_pty ty']))
| Ty_Prod l -> PTtuple (List.map get_pty l)


(* variable environment *)
let bindings : (string, ty) Hashtbl.t = Hashtbl.create 100

let add_user_binding (v, ty) =
  if Hashtbl.mem bindings v then
    failwith @@ Format.sprintf "variable %s already declared" v
  else Hashtbl.add bindings v ty

let add_bindings = Hashtbl.add_seq bindings

let add_local_bindings b = Seq.map (pair_map (Right (fun x -> Local,x))) b |> Hashtbl.add_seq bindings

let remove_bindings = Seq.iter (Hashtbl.remove bindings)

let get_binding_type v f =
  match Hashtbl.find_opt bindings v with
  | None -> failwith @@ Format.sprintf "no why3 binding for identifier '%s'" v
  | Some v -> f v

let ty_suffix s = s ^ "_t"
let history_id = private_var "history"

let history_length =
  PH.(
    P.Tapply (tvar (qualid [ "Length"; "length" ]), tvar (qualid [ history_id ]))
    |> term)

let instant_field ty = private_var (String.sub (get_pp_string pp_cat_ty ty) 0 1)

let nth_h cat = "_prev" ^ instant_field cat

let get_quant_binders vars =
  List.concat
    (List.map
       (fun (v, ty) ->
         PH.one_binder v ?pty:(Option.map get_pty ty))
       vars)

let translate_binop app infix op =
  let id = PH.ident (
      if op = Div then "div" else Ident.op_infix @@ get_pp_string pp_expr_binop op  
    
  ) in
  match op with
  | Add | Sub | Mul | Div -> fun e1 e2 -> app (P.Qident id) [ e1; e2 ]
  | Gt | Lt | Gte | Lte | Eq | Neq | EAnd | EOr -> infix id


  
(* adapted from https://gitlab.inria.fr/why3/why3/-/blob/master/src/parser/parser_common.mly#L229 *)

 let [@warning "-4"] rec reduce_fun_lit f = function
    | [x]  -> f x (snd x)
    | x::xs -> f x (reduce_fun_lit f xs)
    | _ -> assert false (* our grammar disallows empty arrays *)
 
let make_earray (a : P.expr iarray) = 
  let open PH in
  let open P in
  let el = Iarray.to_seq a |> 
  Seq.mapi (fun i e -> Econst (Constant.int_const ~il_kind:Number.ILitDec (BigInt.of_int i)) |> expr, e) |> List.of_seq
  in
  let id ?(id_ats=[]) id_str id_loc = { id_str; id_ats; id_loc } in

  let var_of_string ?(id_ats=[]) nm loc = Qident (id ~id_ats nm loc) |> evar in
  let proxy_atr = ATstr Ident.proxy_attr in
  (* proxy vars for the literal domain/range expressions *)
  let domain_ranga_vars i (e1,e2) =
    let i = string_of_int i in
    var_of_string ~id_ats:[proxy_atr] ("d'i" ^ i) e1.expr_loc,
    var_of_string ~id_ats:[proxy_atr] ("r'i" ^ i) e2.expr_loc in
  let el_proxies = List.mapi domain_ranga_vars el in


  let fun_id_var = PH.ident (if Iarray.length a = 0 then "_" else "x'x") in
    let [@warning "-4"] e2id e = match e with
    | {expr_desc = Eident (Qident id); _} -> id | _ -> assert false in

  let add_expr (e1,e2) e =
    let v_eq_e1 = Einfix (evar (Qident fun_id_var),ident Ident.op_equ,e1) |> expr in
    Eif (v_eq_e1,e2,e) |> expr in


  let binder = (Loc.dummy_position, Some fun_id_var, false, None) in
  let pattern = pat_var fun_id_var in
  let ifte = reduce_fun_lit add_expr el_proxies in
  let efun = Ptree.Efun ([binder], None, pattern, Ity.MaskVisible, empty_spec, ifte) |> expr in


  let mk_let e (d,r) (e1,e2) =
      let e = Elet (e2id r,false,Expr.RKnone,e2,e) |> expr in
      Elet (e2id d,false,Expr.RKnone,e1,e) |> expr
  in
  let b = List.fold_left2 mk_let efun el_proxies el in
  let f = Eattr (ATstr Ident.funlit, b)  in
  eapp (qualid ["init"]) [econst @@ Iarray.length a; expr f]

let rec translate_rexpr (e: ty expr) : P.expr =
  let open P in
  let open PH in
  let loc = get_loc e.label in
  match e.value with
  | True -> expr ~loc Etrue
  | False -> expr ~loc Efalse
  | Int n -> econst n ~loc
  | Prod l -> let l = List.map translate_rexpr l in expr ~loc (Etuple l)
  | Var (s, (cat_ty,_)) ->
    begin
    match cat_ty with
          | Local -> evar ~loc (qualid [ s ])
          | State | Input | Output ->
              eapp (qualid [ s ])
                [ [ get_cat_ty cat_ty ] |> qualid |> evar ~loc ]
    end
  | UnOp (ENot,e) -> Enot (translate_rexpr e) |> expr  ~loc
  | BinOp v -> (
      let e1 = translate_rexpr v.left and e2 = translate_rexpr v.right in
      match v.op with
      | EAnd -> Eand (e1, e2) |> expr
      | EOr -> Eor (e1, e2) |> expr
      | Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq | Neq ->
          translate_binop (eapp ~loc)
            (fun x e1 e2 -> Einnfix (e1, x, e2) |> expr ~loc)
            v.op e1 e2)

  | ArrayCell v ->
      let e = translate_rexpr v.idx in
      eapp ~loc (qualid [ Ident.op_get "" ]) [ e; translate_rexpr v.array ]
  | String s -> P.(Econst (Constant.string_const s)) |> expr ~loc
  | Array a -> make_earray (Iarray.map translate_rexpr a)
  | Real r -> P.(Econst (Constant.real_const_from_string ~neg:false ~radix:r.radix ~int:r.num ~frac:r.frac ~exp:r.exp)) |> expr ~loc



let expr_of_statements (tr_form : 'a -> P.term) (s : ('a, 'b) stmt list) :
    P.expr =
  let open P in
  let open PH in
  let [@warning "-4"] rec tr_seq = function
    | [] -> expr unit_val
    | [ x ] -> tr_stmt x
    | s ->
        List.fold_right
          (fun x y ->
            match (tr_stmt x, y) with
            | { expr_desc = Etuple []; _ }, x 
            | x, { expr_desc = Etuple []; _ }
              ->
                x
            | (_, _) -> Esequence (tr_stmt x, y) |> expr)
          s (expr unit_val)
  and tr_stmt (stmt : ('a, 'b) stmt) =
    let loc = get_loc stmt.label in
    match stmt.value with
    | Assign (e1, e2) ->
        let e2' = translate_rexpr e2 in
        begin
        match e1.value with
        | Var (id, (cty,_)) ->
          let e1',id =
           begin
            match cty with
            | State ->
                ([ get_cat_ty State ] |> qualid |> evar ~loc, id)
            | Local -> ([] |> qualid |> evar ~loc, id)
            | Input | Output as cat ->
                failwith
                @@ Format.sprintf
                    "can't assign expression to stream variable '%s' (%s)" id
                    (get_pp_string pp_cat_ty cat)
            end in
             Eassign [ (e1', Some (qualid [ id ]) , e2') ] |> expr ~loc

        | ArrayCell a -> 
          let array = translate_rexpr a.array
          and idx = translate_rexpr a.idx in
          eapp (qualid [Ident.op_set ""]) [array; idx; e2'] ~loc

        | Int _ | Real _ | True | False | UnOp (_, _) | BinOp _ | Array _ | String _ | Prod _ ->
             failwith "not an assignable expression"
        end 
    | Emit (e, id) ->
        get_binding_type id (fun (cat, _) ->
            let e1, field =
              match cat with 
              | Output ->
                  ( [ get_cat_ty cat ] |> qualid |> evar,
                    Some ([ id ] |> qualid) )
              | Input | State | Local -> failwith @@ Format.asprintf "can't emit to %a variable '%s'" pp_cat_ty cat id
            in
            Eassign [ (e1, field, translate_rexpr e) ] |> expr ~loc)
    | If (e, t, f) ->
        let f = Option.fold ~some:tr_seq f ~none:(expr unit_val) in
        Eif (translate_rexpr e, tr_seq t, f) |> expr ~loc
    | While (e, inv, _v, stmt) ->
        Ewhile (translate_rexpr e, [ tr_form inv ], [], tr_seq stmt)
        |> expr ~loc
  in
  tr_seq s


let get_bop t1 t2 = 
  let open Ptree in
  let open Dterm in 
  function
  | Arrow -> Tbinnop (t1, DTimplies, t2)
  | Equiv -> Tbinnop (t1, DTiff, t2)
  | LAnd -> Tbinnop (t1, DTand, t2)
  | LOr -> Tbinnop (t1, DTor, t2)
  | Program s -> Tinnfix (t1, PH.ident @@ Ident.op_infix s, t2)

  

let rec pterm_of_fol : type a. (a expr -> P.term) -> (a expr predicate, base_ty option) fol -> P.term =
  fun translate_term { value = f; label = loc } -> 
  let pterm_of_fol = pterm_of_fol translate_term in
  let open PH in
  let open P in
  let loc = get_loc loc in
  match f with
  | FOL_True -> term ~loc Ttrue
  | FOL_False -> term ~loc Tfalse
  | FOL_Atom (Atom p) -> translate_term p
  | FOL_Atom (Predicate p) -> tapp (qualid [p.name]) (List.map translate_term p.args)
  | FOL_StdUnary (LNot, t) -> Tnot (pterm_of_fol t) |> term ~loc
  | FOL_StdBinary (t1, bop, t2) -> (
      let t1 = pterm_of_fol t1 in
      let t2 = pterm_of_fol t2 in
      get_bop t1 t2 bop |> term ~loc
  )
  | FOL_StdNary (op,l) ->
    fold_mjoin pterm_of_fol (fun f1 f2 -> get_bop f1 f2 op |> term) (term ~loc Ttrue) l 
  | Forall (v, f) ->
      let locals = List.to_seq v in
      add_local_bindings locals;
      let t = Tquant (DTforall, get_quant_binders v, [], pterm_of_fol f) in
      remove_bindings (Seq.map fst locals);
      term t ~loc
  | Exists (v, f) ->
      let locals = List.to_seq v in
      add_local_bindings locals;
      let t = Tquant (DTexists, get_quant_binders v, [], pterm_of_fol f) in
      remove_bindings (Seq.map fst locals);
      term t ~loc

