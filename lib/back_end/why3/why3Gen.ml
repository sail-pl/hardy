(** {1 Why3 Code Generation} *)

open HardyFrontEnd
open Syntax
open Program
open Shared
open Fol
open Instant
open Printer
open Why3
open Why3Utils
open HardyMisc.Utils
module PH = Ptree_helpers
module P = Ptree

let get_pp_string a b = Format.asprintf "%a" a b

let get_pty ty = Ptree.(PTtyapp (Ptree_helpers.qualid [ty ], []))

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
         let pty =
           get_pty
             (get_pp_string pp_base_ty ty)
         in
         PH.one_binder v ~pty)
       vars)

let translate_binop app infix op =
  let id = PH.ident (Ident.op_infix (Format.asprintf "%a" pp_expr_binop op)) in
  match op with
  | Add | Sub | Mul | Div -> fun e1 e2 -> app (P.Qident id) [ e1; e2 ]
  | Gt | Lt | Gte | Lte | Eq | Neq | EAnd | EOr -> infix id

let rec translate_rexpr (e: ty expr) : P.expr =
  let open P in
  let open PH in
  let loc = get_loc e.label in
  match e.value with
  | True -> expr ~loc Etrue
  | False -> expr ~loc Efalse
  | Int n -> econst n ~loc
  | Var (s, (cat_ty,_)) ->
    begin
    match cat_ty with
          | Local -> evar ~loc (qualid [ s ])
          | _ ->
              eapp (qualid [ s ])
                [ [ get_pp_string pp_cat_ty cat_ty ] |> qualid |> evar ~loc ]
    end
  | UnOp (ENot,e) -> Enot (translate_rexpr e) |> expr  ~loc
  | BinOp v -> (
      let e1 = translate_rexpr v.left and e2 = translate_rexpr v.right in
      match v.op with
      | EAnd -> Eand (e1, e2) |> expr
      | EOr -> Eor (e1, e2) |> expr
      | _ ->
          translate_binop (eapp ~loc)
            (fun x e1 e2 -> Einnfix (e1, x, e2) |> expr ~loc)
            v.op e1 e2)
let translate_lexpr (e : ty expr) : P.expr * string option =
  let open PH in
  let loc = get_loc e.label in
  match e.value with
  | Var (id, (cty,_)) ->
    begin
      match cty with
        | State ->
            ([ get_pp_string pp_cat_ty State ] |> qualid |> evar ~loc, Some id)
        | Local -> ([] |> qualid |> evar ~loc, Some id)
        | cat ->
            failwith
            @@ Format.sprintf
                 "can't assign expression to stream variable '%s' (%s)" id
                 (get_pp_string pp_cat_ty cat)
        end
  | _ -> failwith "not an r-value"


let rec translate_term (e : (instant option * ty) expr) : P.term =
  let open P in
  let open PH in
  let loc = get_loc e.label in

  match e.value with
  | True -> term ~loc Ttrue
  | False -> term ~loc Tfalse
  | Int n -> tconst ~loc n
  | Var (s, (inst,(cat_t,_))) ->
        begin
          match cat_t with
          | Local -> tvar (qualid [ s ])
          | _ -> (
              match inst with
              | Some (Previous 0) | None ->
                  tapp ~loc (qualid [ s ])
                    [ [ get_pp_string pp_cat_ty cat_t ] |> qualid |> tvar ]
              | Some (Previous n) ->
                  let n = tconst (n - 1) in
                  (* last value begins at 0 *)
                  tapp ~loc (qualid [nth_h cat_t]) [ n ; tvar (qualid [ s ]) ]
              | Some (At n) ->
                  let n =
                    Tinnfix
                      ( history_length,
                        Ident.op_infix "-" |> ident,
                        tconst (n + 1) )
                    |> term
                  in
                  tapp ~loc (qualid [nth_h cat_t]) [ n ; tvar (qualid [ s ]) ])
                end
  | UnOp (ENot,t) -> Tnot (translate_term t) |> term  ~loc
    | BinOp v -> (
      let t1 = translate_term v.left and t2 = translate_term v.right in
      match v.op with
      | EAnd -> Tbinnop (t1, Dterm.DTand, t2) |> term ~loc
      | EOr -> Tbinnop (t1, Dterm.DTor, t2) |> term ~loc
      | _ ->
          translate_binop (tapp ~loc)
            (fun x e1 e2 -> Tinnfix (e1, x, e2) |> term ~loc)
            v.op t1 t2)

let expr_of_statements (tr_form : 'a -> P.term) (s : ('a, 'b) stmt list) :
    P.expr =
  let open P in
  let open PH in
  let rec tr_seq = function
    | [] -> expr unit_val
    | [ x ] -> tr_stmt x
    | s ->
        List.fold_right
          (fun x y ->
            match (tr_stmt x, y) with
            | { expr_desc = Etuple []; _ }, x | x, { expr_desc = Etuple []; _ }
              ->
                x
            | _ -> Esequence (tr_stmt x, y) |> expr)
          s (expr unit_val)
  and tr_stmt (stmt : ('a, 'b) stmt) =
    let loc = get_loc stmt.label in
    match stmt.value with
    | Assign (e1, e2) ->
        let e1, id = translate_lexpr e1 in
        let e2 = translate_rexpr e2 in
        Eassign [ (e1, Option.map (fun id -> qualid [ id ]) id, e2) ]
        |> expr ~loc
    | Emit (e, id) ->
        get_binding_type id (fun (cat, _) ->
            let e1, field =
              match cat with
              | Local -> ([ id ] |> qualid |> evar, None)
              | State | Output ->
                  ( [ get_pp_string pp_cat_ty cat ] |> qualid |> evar,
                    Some ([ id ] |> qualid) )
              | Input -> failwith @@ Format.sprintf "can't emit to '%s'" id
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


let get_bop = 
  let open Dterm in 
  function
  | Arrow -> DTimplies
  | Equiv -> DTiff
  | LAnd -> DTand
  | LOr -> DTor

let rec pterm_of_fol
    ({ value = f; label = loc } : ((instant option * ty) expr predicate, base_ty) fol) : P.term =
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
      Tbinnop (t1, get_bop bop, t2) |> term ~loc
  )
  | FOL_StdNary (op,l) -> let op = get_bop op in 
    fold_mjoin pterm_of_fol (fun f1 f2 -> Tbinnop (f1,op,f2) |> term) (term ~loc Ttrue) l 
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
  | ExistsPrev (v, f) ->
      get_binding_type v (fun (cat, bty) ->
          let field = [ instant_field cat ] |> qualid in
          let local_v = (v, (Local, bty)) in
          (* for now, easier to make a local decl and mask the variable *)
          add_bindings Seq.(cons local_v empty);
          let e =
            tapp (qualid [ v ]) [ tapp field [ tvar (qualid [ "_inst" ]) ] ]
          in
          let f = Tlet (ident v, e, pterm_of_fol f) |> term in
          remove_bindings Seq.(cons (fst local_v) empty);
          let f_abs =
            Tquant (Dterm.DTlambda, PH.one_binder "_inst", [], f) |> term ~loc
          in
          let for_some = [ "Quant"; "for_some" ] |> qualid in
          tapp for_some [ f_abs; tvar (qualid [ history_id ]) ])

let pterm_of_inv = pterm_of_fol

module
  M
  (* : Sig.S 
    with type triple_data = Syntax.triple_data_t
     and type fol_data = min_nb_instants  *) =
struct
  (* type in_ty = ty *)
  type triple_data = Syntax.triple_data_t
  type fol_data = min_nb_instants

  (* (in_ty temp_spec_t, (in_ty,fol_data) inst_spec_t, variant_t, unit) program *)
  (* type in_spec = ((in_ty,fol_data) inst_spec_t list) hoare_pair *)

  type in_pgrm = base_program
  type in_setup = (base_spec_t, ty) setup
  type in_body = (base_spec_t, ty) stmt list

  type in_fun =
    ( triple_data,
      (ty, base_ty, min_nb_instants) inst_spec_t HardyMiddleEnd.Sig.formula )
    hoare_triple

  type in_spec = in_fun
  type out_body = P.expr
  type out_pgrm = w3 * P.mlw_file * Pmodule.pmodule Wstdlib.Mstr.t
  type out_decl = P.decl
  type out_fun = out_decl
  type out_setup = out_decl
  type out_spec = P.spec

  let reset () = Hashtbl.clear bindings

  let generate_declarations (env : (cat_ty*base_ty) env) : out_decl list =
    let open P in
    let open PH in
    let mk_decl pty =
      Eany ([], RKnone, Some pty, pat Pwild, MaskVisible, empty_spec) |> expr
    in
    let create_record t (decls : (string * base_ty) list) =
      let fields =
        List.map
          (fun (v, ty) ->
            add_user_binding (v, (t, ty));
            {
              f_loc = Loc.dummy_position;
              f_ident = ident v;
              f_pty = get_pty (get_pp_string pp_base_ty ty);
              (* only inputs are read-only *)
              f_mutable = t <> Input;
              f_ghost = false;
            })
          decls
      in
      let td_def = TDrecord fields in
      let tdecl =
        {
          td_loc = Loc.dummy_position;
          td_ident = ident (get_pp_string pp_cat_ty t |> ty_suffix);
          td_params = [];
          td_vis = Public;
          (* the program does not manipulate the record directly *)
          td_mut = false;
          td_inv = [];
          td_wit = None;
          td_def;
        }
      in
      ( Dtype [ tdecl ],
        Dlet
          ( ident (get_pp_string pp_cat_ty t),
            false,
            RKnone,
            mk_decl (get_pty (get_pp_string pp_cat_ty t |> ty_suffix) ) ))
    in
    let inputs,outputs,vars = Bindings.fold (fun id (ct,bt) (i,o,s) -> match ct with
      | Input -> (id,bt)::i,o,s
      | Output -> i,(id,bt)::o,s
      | State -> i,o,(id,bt)::s
      | Local -> failwith "no local here"
    )
    env.env_variables ([],[],[]) in
    let input_t, i = create_record Input inputs
    and output_t, o = create_record Output outputs
    and state_t, s = create_record State vars in

    let instant_t =
      let td_def =
        TDrecord
          (List.map
             (fun ty ->
               {
                 f_loc = Loc.dummy_position;
                 f_ident = instant_field ty |> ident;
                 (* each field is a pure ghost value, called snapshot: 
        this forbids the mutable types it captures (state and output) to be 
        written to. Hence, such value can only be passed to 
        pure (logic) functions *)
                 f_pty =
                   PTpure
                    (get_pty (get_pp_string pp_cat_ty ty |> ty_suffix));
                 f_mutable = false;
                 f_ghost = true;
               })
             [ Input; Output; State ])
      in
      let tdecl =
        {
          td_loc = Loc.dummy_position;
          td_ident = ident "instant_t";
          td_params = [];
          td_vis = Public;
          td_mut = false;
          td_inv = [];
          td_wit = None;
          td_def;
        }
      in
      Dtype [ tdecl ]
    in

    let hist =
      let ty = (PTtyapp
               ([ "list" ] |> qualid, [ PTtyapp (qualid [ "instant_t" ], []) ])) in
      let d = (Eany ([], RKnone, Some ty, pat Pwild, MaskVisible, empty_spec) |> expr) in

      Dlet
        ( ident history_id,
          true,
          RKfunc,
          d 
        )
    in
    (* (_prev_i n proj) =  (NthNoOpt.nth n _history)._i.proj   *)
    let create_hist_proj cat  = 
    let nth_history n =
      eapp
        (qualid [ "NthNoOpt"; "nth" ])
        [ n; evar (qualid [ history_id ]); ] 
      in
      let body = eapp (qualid ["proj"]) [eapp ([ instant_field cat ] |> qualid) [ nth_history @@ evar (qualid ["n"]) ]] in
      let args = List.append (one_binder "n") (one_binder "proj") in
      let f = Efun (args, None, pat Pwild, Ity.MaskVisible, empty_spec, body) |> expr in
        

      Dlet (ident (nth_h cat),true,RKfunc, f)
    in

    let iproj = create_hist_proj Input 
    and oproj = create_hist_proj Output 
    and sproj = create_hist_proj State  in

    (* let props = List.init 1251 (fun i -> {ld_loc=Loc.dummy_position; ld_ident=ident ("p" ^ string_of_int i); ld_params = []; ld_type = None; ld_def = None}) in  *)
    [ input_t; output_t; state_t; instant_t; i; o; s; hist; iproj; oproj; sproj ;  (* Dlogic props *) ]
    
  let generate_body (b : in_body) : out_body = expr_of_statements pterm_of_inv b

  let generate_function (d : triple_data_t) spec body =
    let open P in
    let open PH in
    Efun ([], None, pat Pwild, Ity.MaskVisible, spec, body) |> expr |> fun m ->
    Dlet (ident d.triple_id, false, Expr.RKnone, m)

  let generate_setup : in_setup option -> out_setup option =
    let open PH in
    let d = { triple_id = "setup" } in
    Option.map (fun s ->
        let bdy = generate_body s.setup_body in
        let spec =
          let f =
            fold_mjoin pterm_of_inv why3_and (term Ttrue) s.setup_ensures
          in
          if f.term_desc = Ttrue then empty_spec
          else
            {
              empty_spec with
              sp_post = [ (Loc.dummy_position, [ (pat Pwild, f) ]) ];
            }
        in
        generate_function d spec bdy)

  let length_assert (n : min_nb_instants) : P.term =
    let open P in
    let open PH in
      Tinnfix
        ( history_length,
          Ident.op_infix (if n.is_max then "=" else ">=") |> ident,
          tconst n.nb_instant )
      |> term

  (** generates WhyML logical expression to represent specification *)
  let generate_spec ((_d, spec) : in_spec) : out_spec =
    let open PH in
    (* let convert conv_data (f, d) =
      let f = pterm_of_fol f in
      Option.fold (conv_data d) ~none:f ~some:(fun l -> why3_and l f)
    in *)

    let sp_pre =
      (* in the precondition, "naked" state variables are always equal 
        to the head of the history, except if we just received our first input, that is, history size is 0
      *)
      let curr cat =
        let eq = Tinnfix
          ( tapp (qualid [nth_h cat]) [ tconst 0; Tquant (Dterm.DTlambda, one_binder "x", [], tvar @@ qualid ["x"]) |> term ],
            Ident.op_infix "=" |> ident,
            tvar (qualid [ get_pp_string pp_cat_ty cat ]) )
        |> term
      in
      P.Tbinnop
        ( length_assert {is_max=false; nb_instant=1},
          DTimplies,
          eq) |> term
    in

      curr State
      :: List.fold_left
           (fun acc -> function
           | {disjuncts=[((f: _),data)]} -> 
              length_assert data :: pterm_of_fol f :: acc
           | d ->  let f = fold_mjoin (fun ((f: _),data : _ inst_spec_t) -> 
                  why3_and (pterm_of_fol f) (length_assert data) 
              ) why3_or (term Ttrue) d.disjuncts
              in f::acc
            ) []
           spec.requires.conjuncts
    in
    let sp_post =
      List.fold_left
        (fun l disj -> match disj with 
        | ({disjuncts=[(f,_)]} : (ty, base_ty, fol_data) inst_spec_t list disjunction) -> 
                 (Loc.dummy_position,[pat Pwild , pterm_of_fol f]):: l
        | d ->  
            let f = fold_mjoin (fun ((f: _),_) -> pterm_of_fol f
            ) why3_or (term Ttrue) d.disjuncts
            in 
             (Loc.dummy_position,[pat Pwild ,f]) :: l 
          )
           []
        spec.ensures.conjuncts          
    in
    { empty_spec with sp_pre; sp_post }

  (** generates WhyML program expression to represent the setup procedure *)
  let generate_program decls setup funs =
    let uses =
      [
        [ "int"; "Int" ];
        [ "ref"; "Ref" ];
        [ "list"; "List" ];
        [ "list"; "Length" ];
        [ "list"; "HdTlNoOpt" ];
        [ "list"; "NthNoOpt" ];
        [ "list"; "Quant" ];
      ]
      |> List.map (PH.use ~import:false)
    in
    let helper_m = (PH.ident "ProgramHelper", uses @ decls) in
    let triples_m =
      ( PH.ident "Program",
        uses
        @ PH.use ~import:false [ "ProgramHelper" ]
          :: add_opt_to_list setup funs )
    in
    let pgrm = P.Modules [ helper_m; triples_m ] in
    let w3 = init_why3 () in
    let w3_modules =
      try
        Why3.Typing.type_mlw_file w3.env [] "???" pgrm 
      with Why3.Loc.Located (loc, e) -> Why3.Loc.error ~loc e
    in
    w3,pgrm,w3_modules

  let write_program name (_,p,_) = print_program p (name ^ ".mlw")
end
