(** {1 Why3 Code Generation} *)

open HardyFrontEnd
open Syntax
open Program
open Shared
open Fol
open Printer
open Why3
open Why3Utils
open HardyMisc.Utils

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
  | None -> failwith @@ Printf.sprintf "no why3 binding for identifier '%s'" v
  | Some v -> f v

let ty_suffix s = s ^ "_t"

let get_quant_binders vars =
  List.concat
    (List.map
       (fun (v, ty) ->
         let pty =
           get_pty
             (function
               | Local, ty -> string_of_base_ty ty
               | State, ty -> string_of_base_ty ty
               | cat, _ -> string_of_cat_ty cat |> ty_suffix)
             ty
         in
         Ptree_helpers.one_binder v ~pty)
       vars)

let get_var (type a) id loc (app : Ptree.qualid -> a list -> a)
    (mk_var : ?loc:Loc.position -> Ptree.qualid -> a) =
  let open Ptree_helpers in
  get_binding_type id (fun (cat, _) ->
      match cat with
      | Local -> mk_var ~loc (qualid [ id ])
      | _ ->
          app (qualid [ id ])
            [ [ string_of_cat_ty cat ] |> qualid |> mk_var ~loc ])

let translate_binop op =
  Ptree_helpers.qualid [ Ident.op_infix (string_of_binop op) ]

let rec translate_expression ({ value = e; loc } : expr) : Ptree.expr =
  let open Ptree in
  let open Ptree_helpers in
  let loc = get_loc loc in
  match e with
  | True -> expr ~loc Etrue
  | False -> expr ~loc Efalse
  | Int n -> econst n ~loc
  | Var s -> get_var s loc eapp evar
  | Read s -> Easref (qualid [ s ]) |> expr ~loc
  | BinOp (e1, binop, e2) ->
      eapp ~loc (translate_binop binop)
        [ translate_expression e1; translate_expression e2 ]

let rec translate_term (e : expr) : Ptree.term =
  let open Ptree in
  let open Ptree_helpers in
  let loc = get_loc e.loc in
  match e.value with
  | True -> term ~loc Ttrue
  | False -> term ~loc Tfalse
  | Int n -> tconst ~loc n
  | Var s -> get_var s loc tapp tvar
  | Read s -> Tasref (qualid [ s ]) |> term ~loc
  | BinOp (e1, binop, e2) ->
      tapp ~loc (translate_binop binop) [ translate_term e1; translate_term e2 ]

let expr_of_statements (tr_form : 'a -> Ptree.term) (s : ('a, 'b) stmt list) :
    Ptree.expr =
  let open Ptree in
  let open Ptree_helpers in
  let rec tr_seq s =
    fold_mjoin tr_stmt (fun x y -> Esequence (x, y) |> expr) (expr unit_val) s
  and tr_stmt (stmt : ('a, 'b) stmt) =
    let loc = get_loc stmt.loc in
    match stmt.value with
    | Assign (id, e) ->
        get_binding_type id (function
          | State, _ ->
              Eassign
                [
                  ( [ string_of_cat_ty State ] |> qualid |> evar,
                    Some ([ id ] |> qualid),
                    translate_expression e );
                ]
              |> expr ~loc
          | cat, _ ->
              failwith
              @@ Format.sprintf
                   "can't assign expression to stream variable '%s' (%s)" id
                   (string_of_cat_ty cat))
    | Emit (e, id) ->
        get_binding_type id (fun (cat, _) ->
            let e1, field =
              match cat with
              | Local -> ([ id ] |> qualid |> evar, None)
              | State | Output ->
                  ( [ string_of_cat_ty cat ] |> qualid |> evar,
                    Some ([ id ] |> qualid) )
              | Input -> failwith @@ Format.sprintf "can't emit to '%s'" id
            in
            Eassign [ (e1, field, translate_expression e) ] |> expr ~loc)
    | If (e, t, f) ->
        let f = Option.fold ~some:tr_seq f ~none:(expr unit_val) in
        Eif (translate_expression e, tr_seq t, f) |> expr ~loc
    | While (e, inv, _v, stmt) ->
        Ewhile (translate_expression e, [ tr_form inv ], [], tr_seq stmt)
        |> expr ~loc
  in
  tr_seq s

let rec pterm_of_fol ({ value = f; loc } : (expr, ty) fol) : Ptree.term =
  let open Ptree_helpers in
  let open Ptree in
  let loc = get_loc loc in
  match f with
  | FOL_True -> term ~loc Ttrue
  | FOL_False -> term ~loc Tfalse
  | Pred p -> translate_term p
  | FOL_Unary (uop, t) -> (
      match uop with Not -> Tnot (pterm_of_fol t) |> term ~loc)
  | FOL_Binary (t1, bop, t2) -> (
      let t1 = pterm_of_fol t1 in
      let t2 = pterm_of_fol t2 in
      match bop with
      | And -> Tbinnop (t1, Dterm.DTand, t2) |> term ~loc
      | Or -> Tbinnop (t1, Dterm.DTor, t2) |> term ~loc
      | Arrow -> Tbinnop (t1, Dterm.DTimplies, t2) |> term ~loc
      | Equiv -> Tbinnop (t1, Dterm.DTiff, t2) |> term ~loc
      | Arithm op -> tapp ~loc (translate_binop op) [ t1; t2 ])
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

let pterm_of_inv = pterm_of_fol

module M : Sig.S with type fun_id = fun_id_t and type in_ty = ty = struct
  type in_ty = ty
  type in_pgrm = (in_ty temp_spec_t, in_ty inst_spec_t, variant_t) program
  type out_pgrm = Ptree.mlw_file
  type out_decl = Ptree.decl
  type fun_id = fun_id_t
  type in_spec = in_ty inst_spec_t list hoare_pair
  type out_spec = Ptree.spec
  type in_setup = (in_ty inst_spec_t, variant_t) setup option
  type out_setup = out_decl
  type in_body = (in_ty inst_spec_t, variant_t) stmt list
  type out_body = Ptree.expr
  type in_fun = (fun_id, in_ty inst_spec_t list) hoare_triple
  type out_fun = out_decl

  let generate_declarations (env : base_ty env) : out_decl list =
    let open Ptree in
    let open Ptree_helpers in
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
              f_pty = get_pty string_of_base_ty ty;
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
          td_ident = ident (string_of_cat_ty t |> ty_suffix);
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
          ( ident (string_of_cat_ty t),
            false,
            RKnone,
            mk_decl (get_pty (fun t -> string_of_cat_ty t |> ty_suffix) t) ) )
    in
    let input_t, i = create_record Input env.env_input
    and output_t, o = create_record Output env.env_output
    and state_t, s = create_record State env.env_variables in

    [ input_t; output_t; state_t; i; o; s; ]

  let generate_body = fun x -> expr_of_statements pterm_of_inv x

  let generate_function name spec body =
    let open Ptree in
    let open Ptree_helpers in
    Efun ([], None, pat Pwild, Ity.MaskVisible, spec, body) |> expr |> fun m ->
    Dlet (ident name.id, false, Expr.RKnone, m)

  let generate_setup (setup : (_ inst_spec_t, _) setup option) =
    let open Ptree_helpers in
    match setup with
    | None -> generate_function { id = "setup" } empty_spec (expr unit_val)
    | Some s ->
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
        generate_function { id = "setup" } spec bdy

  (** generates WhyML logical expression to represent specification *)
  let generate_spec (spec : in_spec) : out_spec =
    let sp_pre = List.map pterm_of_fol spec.requires in
    let post =
      List.map
        (fun e -> (Ptree_helpers.(pat) Pwild, pterm_of_fol e))
        spec.ensures
    in
    {
      Ptree_helpers.empty_spec with
      sp_pre;
      sp_post = [ (Loc.dummy_position, post) ];
    }

  (** generates WhyML program expression to represent the setup procedure *)
  let generate_program decls setup funs =
    let uses =
      [
        [ "int"; "Int" ];
        [ "ref"; "Ref" ];
      ]
    in
    let m =
      ( Ptree_helpers.ident "Program",
        List.fold_left
          (fun l u -> Ptree_helpers.use ~import:false u :: l)
          (decls @ (setup :: funs))
          uses )
    in
    let pgrm = Ptree.Modules [ m ] in
    let () =
      try
        (* let w3 = init_why3 () in *)
        (* let _mods = Why3.Typing.type_mlw_file w3.env [] "???" pgrm in *)
        (* continue *)
        ()
      with Why3.Loc.Located (loc, e) -> Why3.Loc.error ~loc e
    in
    pgrm

  let write_program name p = print_program p (name ^ ".mlw")
end
