open HardySyntax.Locations
open HardySyntax.Types
open HardySyntax.Fol
open HardySyntax.Syntax
open HardySyntax.Printer
open TranslateUtils
open Why3

let get_loc loc =
  match loc with
  | None -> Why3.Mlw_printer.next_pos ()
  | Some l -> Loc.extract l

let why3_and l r = Ptree.Tbinop (l, Dterm.DTand, r) |> Ptree_helpers.term

type id_cat = Var | Input | Output

let bindings : (string, id_cat * ty) Hashtbl.t = Hashtbl.create 100

let add_binding (v, ty) (cat : id_cat) =
  if Hashtbl.mem bindings v then
    failwith @@ Format.sprintf "variable %s already declared" v
  else Hashtbl.add bindings v (cat, ty)

let get_binding_type v = Hashtbl.find_opt bindings v
let unit_val = Why3.Ptree.Etuple []

let translate_binop op =
  Ptree_helpers.qualid [ Ident.op_infix (string_of_binop op) ]

let rec translate_expression ({ value = e; loc } : expr) : Ptree.expr =
  let loc = get_loc loc in
  match e with
  | True -> Ptree_helpers.expr ~loc Etrue
  | False -> Ptree_helpers.expr ~loc Efalse
  | Int n -> Ptree_helpers.econst n ~loc
  (* | Old _ -> Loc.(error ~loc @@ Message "Old only allowed inside formulas") *)
  | Var s -> (
      match get_binding_type s with
      | Some (Input, _) -> Ptree_helpers.([ s ] |> qualid |> evar)
      | Some (Var, _) | Some (Output, _) ->
          let deref = Ptree_helpers.qualid [ Ident.op_prefix "!" ] in
          Ptree_helpers.eapp ~loc deref
            Ptree_helpers.[ [ s ] |> qualid |> evar ]
      | None -> failwith @@ "no why3 binding for variable '" ^ s ^ "'")
  | Read s ->
      Ptree.Easref (Ptree_helpers.qualid [ s ]) |> Ptree_helpers.expr ~loc
  | BinOp (e1, binop, e2) ->
      Ptree_helpers.eapp ~loc (translate_binop binop)
        [ translate_expression e1; translate_expression e2 ]

let rec translate_term (e : expr) : Ptree.term =
  let loc = get_loc e.loc in
  match e.value with
  | True -> Ptree_helpers.term ~loc Ttrue
  | False -> Ptree_helpers.term ~loc Tfalse
  | Int n -> Ptree_helpers.tconst ~loc n
  (* | Old s -> 	H.term ~loc H.(Tat (translate_term {value=Var s;loc=e.loc},ident ~loc Dexpr.old_label)) *)
  | Var s -> (
      match get_binding_type s with
      | Some (Input, _) -> Ptree_helpers.([ s ] |> qualid |> tvar)
      | Some (Var, _) | Some (Output, _) ->
          let deref = Ptree_helpers.qualid [ Ident.op_prefix "!" ] in
          Ptree_helpers.tapp ~loc deref
            Ptree_helpers.[ [ s ] |> qualid |> tvar ]
      | None -> failwith @@ "no why3 binding '" ^ s ^ "'")
  | Read s ->
      Ptree.Tasref (Ptree_helpers.qualid [ s ]) |> Ptree_helpers.term ~loc
  | BinOp (e1, binop, e2) ->
      Ptree_helpers.tapp ~loc (translate_binop binop)
        [ translate_term e1; translate_term e2 ]

let rec translate_statements (tr_form : invariant -> Ptree.term) (s : stmt list)
    : Ptree.expr =
  let open Ptree in
  let open Ptree_helpers in
  let translate_statements = translate_statements tr_form in
  let aux { value = s; loc } =
    let loc = get_loc loc in
    match s with
    | Assign (id, e) ->
        let assgn = qualid [ Ident.op_infix ":=" ] in
        eapp ~loc assgn [ [ id ] |> qualid |> evar; translate_expression e ]
    | Emit (id, e) ->
        Eassign [ (translate_expression e, None, [ id ] |> qualid |> evar) ]
        |> expr ~loc (* will need to be treated differently *)
    | If (e, t, f) ->
        let f =
          Option.fold ~some:translate_statements f ~none:(expr unit_val)
        in
        Eif (translate_expression e, translate_statements t, f) |> expr ~loc
    | While (e, inv, _v, stmt) ->
        Ewhile
          ( translate_expression e,
            [ tr_form inv ],
            [],
            translate_statements stmt )
        |> expr ~loc
  in
  fold_mjoin aux (fun x y -> Esequence (x, y) |> expr) (expr unit_val) s

let get_pty ty =
  let ty = string_of_ty ty in
  Ptree.(PTtyapp (Ptree_helpers.qualid [ ty ], []))

let generate_declarations (env : env) =
  let open Ptree in
  let open Ptree_helpers in
  let get_exp ty =
    Eany ([], RKnone, Some (get_pty ty), pat Pwild, MaskVisible, empty_spec)
    |> expr
  in

  (* inputs are r *)
  List.fold_right
    (fun (v, ty) decls ->
      add_binding (v, ty) Input;
      Dlet (ident v, false, RKnone, get_exp ty) :: decls)
    env.env_input []
  |> (* outputs are rw *)
  List.fold_right
    (fun (v, ty) decls ->
      add_binding (v, ty) Output;
      Dlet (ident v, false, RKnone, eapply (expr Eref) (get_exp ty)) :: decls)
    env.env_output
  |> (* vars are rw *)
  List.fold_right
    (fun (v, ty) decls ->
      add_binding (v, ty) Var;
      Dlet (ident v, false, RKnone, eapply (expr Eref) (get_exp ty)) :: decls)
    env.env_variables

let rec pterm_of_fol ({ value = f; loc } : expr fol) : Ptree.term =
  let open Ptree_helpers in
  let open Ptree in
  let loc = get_loc loc in
  match f with
  | FOL_True -> term ~loc Ttrue
  | FOL_False -> term ~loc Tfalse
  | Pred p -> translate_term p
  | FOL_Unary (uop, t) -> (
      match uop with Not -> Tnot (pterm_of_fol t) |> term ~loc)
  | FOL_Binary (t1, bop, t2) ->
      let t1 = pterm_of_fol t1 in
      let t2 = pterm_of_fol t2 in
      let bop =
        match bop with
        | And -> Dterm.DTand
        | Or -> Dterm.DTor
        | Arrow -> Dterm.DTimplies
        | Equiv -> Dterm.DTiff
        | Xor -> failwith "todo xor"
        | Arithm _ -> failwith "todo Arithm"
      in
      Tbinop (t1, bop, t2) |> term ~loc
  | Forall (v, f) ->
      Tquant
        ( DTforall,
          List.concat
            (List.map
               (fun (v, ty) ->
                 let pty = get_pty ty in
                 one_binder v ~pty)
               v),
          [],
          pterm_of_fol f )
      |> term ~loc
  | Exists (v, f) ->
      Tquant
        ( DTexists,
          List.concat
            (List.map
               (fun (v, ty) ->
                 let pty = get_pty ty in
                 one_binder v ~pty)
               v),
          [],
          pterm_of_fol f )
      |> term ~loc

let mk_fun name spec body =
  let open Ptree in
  let open Ptree_helpers in
  Efun ([], None, pat Pwild, Ity.MaskVisible, spec, body) |> expr |> fun m ->
  Dlet (ident name, false, Expr.RKnone, m)

let make_setup (setup : setup option) =
  let open Ptree_helpers in
  match setup with
  | None -> mk_fun "setup" empty_spec (expr unit_val)
  | Some s ->
      let bdy = translate_statements pterm_of_fol s.setup_body in
      let spec =
        let f = fold_mjoin pterm_of_fol why3_and (term Ttrue) s.setup_ensures in
        if f.term_desc = Ttrue then empty_spec
        else
          {
            empty_spec with
            sp_post = [ (Loc.dummy_position, [ (pat Pwild, f) ]) ];
          }
      in
      mk_fun "setup" spec bdy

let to_spec (l : expr fol list hoare_pair list) : Ptree.spec list =
  List.map
    (fun h ->
      let sp_pre = List.map pterm_of_fol h.requires in
      let post =
        List.map
          (fun e -> (Ptree_helpers.(pat) Pwild, pterm_of_fol e))
          h.ensures
      in
      {
        Ptree_helpers.empty_spec with
        sp_pre;
        sp_post = [ (Loc.dummy_position, post) ];
      })
    l
