(** {1 Why3 Code Generation} *)

open HardyFrontEnd
open Syntax.Program
open Syntax.Shared
open Syntax.Fol
open Printer
open Why3
open Why3Utils
open HardyMisc.Utils

type id_cat = Var | Input | Output

let string_of_cat = function
  | Input -> "inputs"
  | Output -> "outputs"
  | Var -> "state"

(* variable environment *)
let bindings : (string, id_cat * ty) Hashtbl.t = Hashtbl.create 100

let add_binding (v, ty) (cat : id_cat) =
  if Hashtbl.mem bindings v then
    failwith @@ Format.sprintf "variable %s already declared" v
  else Hashtbl.add bindings v (cat, ty)

let get_binding_type v = Hashtbl.find_opt bindings v
(* let deref = Ptree_helpers.qualid [ Ident.op_prefix "!" ] *)
(* let assgn = Ptree_helpers.qualid [ Ident.op_infix ":=" ] *)
(* let hd = Ptree_helpers.qualid [ "List"; "hd" ] *)
(* let prev = Ptree_helpers.qualid [ "prev" ] *)

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
  | Prev _ -> Loc.(error ~loc @@ Message "Prev only allowed inside formulas")
  | Var s -> (
      match get_binding_type s with
      | Some (t, _) ->
          eapp ~loc ([ s ] |> qualid) [ [ string_of_cat t ] |> qualid |> evar ]
      | None -> failwith @@ "no why3 binding for variable '" ^ s ^ "'")
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
  | Prev _s ->
      tconst 2
      (* Tapply (term ~loc (Tident prev),translate_term { value = Var s; loc = e.loc }) *)
  | Var s -> (
      match get_binding_type s with
      | Some (t, _) ->
          tapp ~loc ([ s ] |> qualid) [ [ string_of_cat t ] |> qualid |> tvar ]
      | None -> failwith @@ "no why3 binding '" ^ s ^ "'")
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
    | Assign (id, e) -> (
        match get_binding_type id with
        | Some ((Var as t), _) ->
            Eassign
              [
                ( [ string_of_cat t ] |> qualid |> evar,
                  Some ([ id ] |> qualid),
                  translate_expression e );
              ]
            |> expr ~loc
        | Some (t, _) ->
            failwith
            @@ Format.sprintf
                 "can't assign expression to stream variable '%s' (%s)" id
                 (string_of_cat t)
        | None -> failwith @@ "no why3 binding for variable '" ^ id ^ "'")
    | Emit (e, id) -> (
        match get_binding_type id with
        | Some ((Var as t), _) | Some ((Output as t), _) ->
            Eassign
              [
                ( [ string_of_cat t ] |> qualid |> evar,
                  Some ([ id ] |> qualid),
                  translate_expression e );
              ]
            |> expr ~loc
        | Some (Input, _) -> failwith @@ Format.sprintf "can't emit to '%s'" id
        | None -> failwith @@ "no why3 binding for variable '" ^ id ^ "'")
    | If (e, t, f) ->
        let f = Option.fold ~some:tr_seq f ~none:(expr unit_val) in
        Eif (translate_expression e, tr_seq t, f) |> expr ~loc
    | While (e, inv, _v, stmt) ->
        Ewhile (translate_expression e, [ tr_form inv ], [], tr_seq stmt)
        |> expr ~loc
  in
  tr_seq s

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
                 let pty = get_pty string_of_ty ty in
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
                 let pty = get_pty string_of_ty ty in
                 one_binder v ~pty)
               v),
          [],
          pterm_of_fol f )
      |> term ~loc

let pterm_of_inv = pterm_of_fol

module Why3ProgramBuilder : Sig.S with type fun_id = string = struct
  type in_pgrm = base_program
  type out_pgrm = Ptree.mlw_file
  type out_decl = Ptree.decl
  type fun_id = string
  type in_spec = inst_spec_t list hoare_pair
  type out_spec = Ptree.spec
  type in_setup = (inst_spec_t, variant_t) setup option
  type out_setup = out_decl
  type in_body = (inst_spec_t, variant_t) stmt list
  type out_body = Ptree.expr
  type in_fun = (fun_id, inst_spec_t list) hoare_triple
  type out_fun = out_decl

  let generate_declarations (env : env) : out_decl list =
    let open Ptree in
    let open Ptree_helpers in
    let mk_decl pty =
      Eany ([], RKnone, Some pty, pat Pwild, MaskVisible, empty_spec) |> expr
    in
    let ty_suffix s = s ^ "_t" in

    let create_record t decls =
      let fields =
        List.map
          (fun (v, ty) ->
            add_binding (v, ty) t;
            {
              f_loc = Loc.dummy_position;
              f_ident = ident v;
              f_pty = get_pty string_of_ty ty;
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
          td_ident = ident (string_of_cat t |> ty_suffix);
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
          ( ident (string_of_cat t),
            false,
            RKnone,
            mk_decl (get_pty (fun t -> string_of_cat t |> ty_suffix) t) ) )
    in

    let input_t, i = create_record Input env.env_input
    and output_t, o = create_record Output env.env_output
    and state_t, s = create_record Var env.env_variables in

    let ios_t =
      List.map
        (fun t -> get_pty (fun t -> string_of_cat t |> ty_suffix) t)
        [ Input; Output; Var ]
    in

    let hist =
      Dlet
        ( ident "history",
          true,
          RKnone,
          mk_decl (PTtyapp ([ "list" ] |> qualid, [ PTtuple ios_t ])) )
    in

    [ input_t; output_t; state_t; i; o; s; hist ]

  let generate_body = fun x -> expr_of_statements pterm_of_inv x

  let generate_function name spec body =
    let open Ptree in
    let open Ptree_helpers in
    Efun ([], None, pat Pwild, Ity.MaskVisible, spec, body) |> expr |> fun m ->
    Dlet (ident name, false, Expr.RKnone, m)

  let generate_setup (setup : (inst_spec_t, _) setup option) =
    let open Ptree_helpers in
    match setup with
    | None -> generate_function "setup" empty_spec (expr unit_val)
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
        generate_function "setup" spec bdy

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
        [ "list"; "List" ];
        [ "list"; "HdTlNoOpt" ];
        [ "list"; "NthNoOpt" ];
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
        let w3 = init_why3 () in
        let _mods = Why3.Typing.type_mlw_file w3.env [] "???" pgrm in
        (* continue *)
        ()
      with Why3.Loc.Located (loc, e) -> Why3.Loc.error ~loc e
    in
    pgrm

  let write_program name p = print_program p (name ^ ".mlw")
end
