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

let rec get_pty (to_str : 'a -> string) = function
  | ( Ty_Bool
    | Ty_String (* string are hashed and represented as integers for now *)
    | Ty_Int ) as ty ->
      Ptree.(PTtyapp (Ptree_helpers.qualid [ to_str ty ], []))
  | Ty_Array (ty, _) ->
      Ptree.(PTtyapp (Ptree_helpers.qualid [ "array" ], [ get_pty to_str ty ]))
  | Ty_Prod l -> PTtuple (List.map (get_pty to_str) l)

(* variable environment *)
let bindings : (string, ty) Hashtbl.t = Hashtbl.create 100

let add_user_binding (v, ty) =
  if Hashtbl.mem bindings v then
    failwith @@ Format.sprintf "variable %s already declared" v
  else Hashtbl.add bindings v ty

let add_bindings = Hashtbl.add_seq bindings
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

let history_head =
  PH.(
    tapp
      (qualid [ "NthNoOpt"; "nth" ])
      [ tconst 0; tvar (qualid [ history_id ]) ])

let instant_field ty = private_var (String.sub (get_pp_string pp_cat_ty ty) 0 1)

let get_quant_binders vars =
  List.concat
    (List.map
       (fun (v, (cat, ty)) ->
         let pty =
           get_pty
             (fun ty ->
               match (cat, ty) with
               | Local, ty | State, ty -> get_pp_string pp_base_ty ty
               | cat, _ -> get_pp_string pp_cat_ty cat |> ty_suffix)
             ty
         in
         PH.one_binder v ~pty)
       vars)

let translate_binop app infix op =
  let id = PH.ident (Ident.op_infix (Format.asprintf "%a" pp_expr_binop op)) in
  match op with
  | Add | Sub | Mul | Div -> fun e1 e2 -> app (P.Qident id) [ e1; e2 ]
  | Gt | Lt | Gte | Lte | Eq | Neq | EAnd | EOr -> infix id

let rec make_elist = function
  | [] -> PH.(evar (qualid [ "Nil" ]))
  | h :: t -> PH.(eapp (qualid [ "Cons" ]) [ h; make_elist t ])

let rec make_tlist = function
  | [] -> PH.(tvar (qualid [ "Nil" ]))
  | h :: t -> PH.(tapp (qualid [ "Cons" ]) [ h; make_tlist t ])

(* no: instead, use array.Init.init and unroll each element of the list for each index of *)

let rec translate_rexpr (e : unit expr) : P.expr =
  let open P in
  let open PH in
  let loc = get_loc e.label in
  match e.value with
  | True -> expr ~loc Etrue
  | False -> expr ~loc Efalse
  | Int n -> econst n ~loc
  | Prod _l -> failwith "todo tuple"
  | Var (s, ()) ->
      get_binding_type s (fun (cat, _) ->
          match cat with
          | Local -> evar ~loc (qualid [ s ])
          | _ ->
              eapp (qualid [ s ])
                [ [ get_pp_string pp_cat_ty cat ] |> qualid |> evar ~loc ])
  | UnOp (ENot, e) -> Enot (translate_rexpr e) |> expr ~loc
  | BinOp v -> (
      let e1 = translate_rexpr v.left and e2 = translate_rexpr v.right in
      match v.op with
      | EAnd -> Eand (e1, e2) |> expr
      | EOr -> Eor (e1, e2) |> expr
      | _ ->
          translate_binop (eapp ~loc)
            (fun x e1 e2 -> Einnfix (e1, x, e2) |> expr ~loc)
            v.op e1 e2)
  | ArrayCell v ->
      let e = translate_rexpr v.idx in
      eapp ~loc (qualid [ Ident.op_get "" ]) [ e; translate_rexpr v.array ]
  | String s -> econst (String.hash s) ~loc
  | Array l -> List.map translate_rexpr l |> make_elist

let translate_lexpr (e : unit expr) : P.expr * string option =
  let open PH in
  let loc = get_loc e.label in
  match e.value with
  | Var (id, ()) ->
      get_binding_type id (function
        | State, _ ->
            ([ get_pp_string pp_cat_ty State ] |> qualid |> evar ~loc, Some id)
        | Local, _ -> ([] |> qualid |> evar ~loc, Some id)
        | cat, _ ->
            failwith
            @@ Format.sprintf
                 "can't assign expression to stream variable '%s' (%s)" id
                 (get_pp_string pp_cat_ty cat))
  | ArrayCell v ->
      let e = translate_rexpr v.idx in
      (eapp ~loc (qualid [ Ident.op_get "" ]) [ e; translate_rexpr v.array ], None)
  | _ -> failwith "not an r-value"

let rec translate_term (e : instant option expr) : P.term =
  let open P in
  let open PH in
  let loc = get_loc e.label in

  match e.value with
  | True -> term ~loc Ttrue
  | False -> term ~loc Tfalse
  | Int n -> tconst ~loc n
  | Var (s, t) ->
      get_binding_type s (fun (cat, _) ->
          match cat with
          | Local -> tvar (qualid [ s ])
          | _ -> (
              let field = [ instant_field cat ] |> qualid in
              let nth = [ "NthNoOpt"; "nth" ] |> qualid in
              match t with
              | Some (Previous 0) | None ->
                  tapp ~loc (qualid [ s ])
                    [ [ get_pp_string pp_cat_ty cat ] |> qualid |> tvar ]
              | Some (Previous n) ->
                  let n = tconst (n - 1) in
                  (* last value begins at 0 *)
                  let inst = tapp nth [ n; tvar (qualid [ history_id ]) ] in
                  tapp ~loc (qualid [ s ]) [ tapp field [ inst ] ]
              | Some (At n) ->
                  let n =
                    Tinfix
                      ( history_length,
                        Ident.op_infix "-" |> ident,
                        tconst (n + 1) )
                    |> term
                  in
                  let inst = tapp nth [ n; tvar (qualid [ history_id ]) ] in
                  tapp ~loc (qualid [ s ]) [ tapp field [ inst ] ]))
  | UnOp (ENot, t) -> Tnot (translate_term t) |> term ~loc
  | BinOp v -> (
      let t1 = translate_term v.left and t2 = translate_term v.right in
      match v.op with
      | EAnd -> Tbinop (t1, Dterm.DTand, t2) |> term ~loc
      | EOr -> Tbinop (t1, Dterm.DTor, t2) |> term ~loc
      | _ ->
          translate_binop (tapp ~loc)
            (fun x e1 e2 -> Tinnfix (e1, x, e2) |> term ~loc)
            v.op t1 t2)
  | Array l -> List.map translate_term l |> make_tlist
  | String s -> tconst ~loc (String.hash s)
  | ArrayCell v ->
      tapp ~loc
        (qualid [ Ident.op_get "" ])
        [ translate_term v.idx; translate_term v.array ]
  | Prod _ -> failwith "todo prod"

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
    | Clear _e -> failwith "todo"
    | Emit (e, id) ->
        let e = translate_rexpr e in
        get_binding_type id (fun (cat, _) ->
            let e1, field =
              match cat with
              | Local -> ([ id ] |> qualid |> evar, None)
              | State | Output ->
                  ( [ get_pp_string pp_cat_ty cat ] |> qualid |> evar,
                    Some ([ id ] |> qualid) )
              | Input -> failwith @@ Format.sprintf "can't emit to '%s'" id
            in
            Eassign [ (e1, field, e) ] |> expr ~loc)
    | If (e, t, f) ->
        let f = Option.fold ~some:tr_seq f ~none:(expr unit_val) in
        Eif (translate_rexpr e, tr_seq t, f) |> expr ~loc
    | When (id,t,f) -> 
      let f = Option.fold ~some:tr_seq f ~none:(expr unit_val) in
      let t = tr_seq t in 
      Ematch ([id] |> qualid |> evar, [(pat (Papp (qualid ["Some"], [pat (Pvar (ident id))])), t); (pat Pwild,f)], []) |> expr ~loc
    | While (e, inv, _v, stmt) ->
        Ewhile (translate_rexpr e, [ tr_form inv ], [], tr_seq stmt)
        |> expr ~loc
  in
  tr_seq s

let rec pterm_of_fol
    ({ value = f; label = loc } : (instant option expr, ty) fol) : P.term =
  let open PH in
  let open P in
  let loc = get_loc loc in
  match f with
  | FOL_True -> term ~loc Ttrue
  | FOL_False -> term ~loc Tfalse
  | FOL_Atom p -> translate_term p
  | FOL_StdUnary (LNot, t) -> Tnot (pterm_of_fol t) |> term ~loc
  | FOL_StdBinary (t1, bop, t2) -> (
      let t1 = pterm_of_fol t1 in
      let t2 = pterm_of_fol t2 in
      match bop with
      | Arrow -> Tbinop (t1, Dterm.DTimplies, t2) |> term ~loc
      | Equiv -> Tbinop (t1, Dterm.DTiff, t2) |> term ~loc
      | LAnd -> Tbinop (t1, Dterm.DTand, t2) |> term ~loc
      | LOr -> Tbinop (t1, Dterm.DTor, t2) |> term ~loc)
  | Forall (v, f) ->
      let locals = List.to_seq v in
      add_bindings locals;
      let t = Tquant (DTforall, get_quant_binders v, [], pterm_of_fol f) in
      remove_bindings (Seq.map fst locals);
      term t ~loc
  | Exists (v, f) ->
      let locals = List.to_seq v in
      add_bindings locals;
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

module M :
  Sig.S
    with type triple_data = Syntax.triple_data_t
     and type fol_data = min_nb_instants = struct
  (* type in_ty = ty *)
  type triple_data = Syntax.triple_data_t
  type fol_data = min_nb_instants

  (* (in_ty temp_spec_t, (in_ty,fol_data) inst_spec_t, variant_t, unit) program *)
  (* type in_spec = ((in_ty,fol_data) inst_spec_t list) hoare_pair *)

  type in_pgrm = base_program

  type in_fun =
    ( triple_data,
      (Shared.ty, fol_data) inst_spec_t U.disjunction U.conjunction )
    hoare_triple

  type in_spec = in_fun
  type out_body = P.expr
  type out_pgrm = P.mlw_file
  type out_decl = P.decl
  type out_fun = out_decl
  type out_setup = out_decl
  type out_spec = P.spec

  let generate_declarations (env : base_ty env) : out_decl list =
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
              f_pty = get_pty (get_pp_string pp_base_ty) ty;
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
            mk_decl
              (get_pty
                 (fun _ -> get_pp_string pp_cat_ty t |> ty_suffix)
                 Ty_Bool) ) )
    in
    let input_t, i = create_record Input env.env_input
    and output_t, o = create_record Output env.env_output
    and state_t, s = create_record State env.env_variables in

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
                     (get_pty
                        (fun _ -> get_pp_string pp_cat_ty ty |> ty_suffix)
                        Ty_Bool);
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
      Dlet
        ( ident history_id,
          true,
          RKnone,
          mk_decl
            (PTtyapp
               ([ "list" ] |> qualid, [ PTtyapp (qualid [ "instant_t" ], []) ]))
        )
    in

    [ input_t; output_t; state_t; instant_t; i; o; s; hist ]

  let generate_body (p : in_pgrm) (d : triple_data) : out_body =
    let _node = find_node p.prog_nodes d.triple_node_id  in
    (* expr_of_statements pterm_of_inv node.node_body *)
    expr_of_statements pterm_of_inv []

  let generate_function (_p : in_pgrm) (d : triple_data_t) spec body =
    let open P in
    let open PH in
    Efun ([], None, pat Pwild, Ity.MaskVisible, spec, body) |> expr |> fun m ->
    Dlet (ident d.triple_id, false, Expr.RKnone, m)

  (* let generate_setup : in_setup option -> out_setup option =
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
        generate_function d spec bdy) *)

  let length_assert (n : min_nb_instants) : P.term option =
    let open P in
    let open PH in
    if not n.is_max then
      (* for now, we assume knowing the minimal history length isn't helpful *)
      None
    else
      Tinfix
        ( history_length,
          Ident.op_infix (if n.is_max then "=" else ">=") |> ident,
          tconst n.nb_instant )
      |> term |> Option.some

  (** generates WhyML logical expression to represent specification *)
  let generate_spec ((_d, spec) : in_spec) : out_spec =
    let open PH in
    let convert conv_data (f, d) =
      let f = pterm_of_fol f in
      Option.fold (conv_data d) ~none:f ~some:(fun l -> why3_and l f)
    in

    let sp_pre =
      (* in the precondition, "naked" variables except inputs are always equal 
        to the head of the history

        note: adding this might not be needed
      *)
      let curr cat =
        Tinfix
          ( tapp ([ instant_field cat ] |> qualid) [ history_head ],
            Ident.op_infix "=" |> ident,
            tvar (qualid [ get_pp_string pp_cat_ty cat ]) )
        |> term
      in

      curr State :: curr Output
      :: List.map
           (fun disj ->
             fold_mjoin (convert length_assert) why3_or (term Ttrue)
               disj.disjunct)
           spec.requires.conjunct
    in
    let post =
      List.map
        (fun disj ->
          ( pat Pwild,
            fold_mjoin
              (convert (fun _ -> None))
              why3_or (term Ttrue) disj.disjunct ))
        spec.ensures.conjunct
    in
    { empty_spec with sp_pre; sp_post = [ (Loc.dummy_position, post) ] }

  (** generates WhyML program expression to represent the setup procedure *)
  let generate_program decls funs =
    let uses =
      [
        [ "int"; "Int" ];
        [ "ref"; "Ref" ];
        [ "list"; "List" ];
        [ "list"; "Length" ];
        [ "list"; "HdTlNoOpt" ];
        [ "list"; "NthNoOpt" ];
        [ "list"; "Quant" ];
        [ "array"; "Array" ];
      ]
    in
    let m =
      ( PH.ident "Program",
        List.fold_left
          (fun l u -> PH.use ~import:false u :: l)
          (decls @ funs) uses )
    in
    let pgrm = P.Modules [ m ] in
    let () =
      try
        let w3 = init_why3 () in
        let _mods = Why3.Typing.type_mlw_file w3.env [] "???" pgrm in
        (* continue *)
        ()
      with Why3.Loc.Located (loc, e) -> Why3.Loc.error ~loc e
    in
    pgrm

  let write_program name p = print_program p (name ^ ".mlw")
end
