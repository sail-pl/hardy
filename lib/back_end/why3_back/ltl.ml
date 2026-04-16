(** {1 Why3 Code Generation} *)

open HardyFrontEnd
open Syntax
open Shared
open Fol
open Instant
open Why3
open Utils
open HardyMisc.Utils
open Program

open Common
open Ltl_spec


let rec translate_term (e : (instant option * ty) expr) : P.term =
  let open P in
  let open PH in
  let loc = get_loc e.label in

  match e.value with
  | True -> term ~loc Ttrue
  | False -> term ~loc Tfalse
  | Int n -> tconst ~loc n
  | Real r -> P.(Tconst (Constant.real_const_from_string ~neg:false ~radix:r.radix ~int:r.num ~frac:r.frac ~exp:r.exp)) |> term ~loc
  | Var (s, (inst,(cat_t,_))) ->
        begin
          match cat_t with
          | Local -> tvar (qualid [ s ])
          | State | Input | Output -> (
              match inst with
              | Some (Previous 0) | None ->
                  tapp ~loc (qualid [ s ])
                    [ [ get_cat_ty cat_t] |> qualid |> tvar ]
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
    | Add | Sub | Mul | Div | Gt | Lt | Gte | Lte | Eq | Neq ->
        translate_binop (tapp ~loc)
          (fun x e1 e2 -> Tinnfix (e1, x, e2) |> term ~loc)
          v.op t1 t2)
  | Array _ -> failwith "array literals are not supported within Why3 terms"
  | String s -> P.(Tconst (Constant.string_const s)) |> term ~loc
  | ArrayCell a ->
    tapp ~loc (qualid [Ident.op_get ""]) [translate_term a.array ; translate_term a.idx]
  | Prod l -> let l  = List.map translate_term l in term ~loc (Ttuple l)


let pterm_of_inv = pterm_of_inv translate_term 
let pterm_of_fol = pterm_of_fol translate_term  

module
  M
  : BackSig.S with 
  type in_fun = cnf_data and
  type triple_data = triple_data and
  type local_spec = base_spec_t and
  type temp_spec = ((FrontSig.temp_f_prop, instant option * ty, base_ty) temp_spec_t, FrontSig.temp_f_prop)  labeled  and
  type in_spec = (((instant option * Shared.ty, Shared.base_ty) fol_t, fol_data) U.labeled, formula_data) labeled cnf and
  type out_pgrm = P.mlw_file 
= struct

  type local_spec = base_spec_t
  type temp_spec = ((FrontSig.temp_f_prop, instant option * ty, base_ty) temp_spec_t, FrontSig.temp_f_prop) labeled

  type formula = ((instant option * Shared.ty, Shared.base_ty) fol_t, fol_data) U.labeled

  type in_pgrm = (temp_spec, unit, base_spec_t, ty, ty env) program
  type in_setup = (base_spec_t, ty) setup
  type in_body = (base_spec_t, ty) stmt list
  type in_spec = (formula, formula_data) labeled cnf
  type in_fun = cnf_data

  type nonrec triple_data = triple_data

  type out_body = P.expr
  type out_pgrm = P.mlw_file
  type out_decl = P.decl
  type out_fun = out_decl
  type out_setup = out_decl
  type out_spec = P.spec

  type processed_defs = {
    processed_decls : out_decl list ;
    processed_setup : out_setup option ;
    processed_functions: out_fun list ;
  }

  let reset () = Hashtbl.clear bindings

  let generate_declarations (env : ty env) : out_decl list =
    let open P in
    let open PH in
    let mk_decl pty =
      Eany ([], RKnone, Some pty, pat Pwild, MaskVisible, empty_spec) |> expr
    in
    let create_record t (decls : (string * base_ty option) list) =
      let fields =
        List.map
          (fun (v, ty) ->
            add_user_binding (v, (t, ty));
            {
              f_loc = Loc.dummy_position;
              f_ident = ident v;
              f_pty = get_pty (Option.get ty) (* syntax disallows empty type here *) ;
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
          td_ident = ident (get_cat_ty t |> ty_suffix);
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
          ( ident (get_cat_ty t),
            false,
            RKnone,
            mk_decl (get_custom_pty (get_cat_ty t |> ty_suffix) ) ))
    in
    let inputs,outputs,vars = Bindings.fold (fun id (ct,bt) (i,o,s) -> match ct with
      | Input -> (id,bt)::i,o,s
      | Output -> i,(id,bt)::o,s
      | State -> i,o,(id,bt)::s
      | Local -> assert false (* no locals here *)
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
                    (get_custom_pty (get_cat_ty ty |> ty_suffix));
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

  let length_assert (n : min_nb_instants) : P.term =
    let open P in
    let open PH in
      Tinnfix
        ( history_length,
          Ident.op_infix (if n.is_max then "=" else ">=") |> ident,
          tconst n.nb_instant )
      |> term

  (** generates WhyML logical expression to represent specification *)
  let generate_spec (spec : in_spec hoare_pair) (d: triple_data) : out_spec =
    (* spec.data.min.nb_instants is None iff spec is not temporal (e.g. generating setup spec) *)
    let open PH in

    let sp_pre =
      let history =
        let state_eq_head = 
        (* in the precondition, "naked" state variables are always equal 
          to the head of the history, except if we just received our first input, that is, history size is 0
            *)
          Tinnfix
          ( tapp (qualid [nth_h State]) [ tconst 0; Tquant (Dterm.DTlambda, one_binder "x", [], tvar @@ qualid ["x"]) |> term ],
            Ident.op_equ |> ident,
            tvar (qualid [ get_cat_ty State ]) )
        |> term
        in 

        let imp = P.Tbinnop ( length_assert {is_max=false; nb_instant=1}, DTimplies, state_eq_head) |> term in
        (*
          assert min history length: 
          useful in case only a function invariant is set (there would be no temporal formula to get the information from)
        *)
        Option.fold ~none:imp ~some:(fun inst -> 
          if inst.nb_instant >= 1 then 
            why3_and state_eq_head (length_assert inst)
          else 
            length_assert inst
        ) (Some d.nb_instants)

      and inv = 
        (* if the current node is the first node with no incoming transition, i.e. there is no history, 
          we must not assume the provided invariants to hold.
          Note: it is also ignored when there is no history information i.e. spec.data.min_nb_instants = None
        *)
        Option.fold ~none:[] ~some:(fun inst -> 
          if inst.nb_instant = 0 && inst.is_max then []
          else 
            List.map (fun inv ->
              (* invariant parameterized by outputs are about the previous output in the history when used as a precondition, 
                  which means they also depend on the previous input and state  
                  (state is kept from one instant to the other so it is not useful to adjust it).
              *)
              pterm_of_fol (map_fol_pred (map_expr Fun.id Fun.id) 
              inv)
            ) d.invariants
        ) (Some d.nb_instants)
      in
      history :: List.fold_left
        (fun acc (f: (formula, formula_data)  labeled disjunction) -> match f with
        | {disjuncts=[f]} -> 
            pterm_of_fol f.value.value :: acc
        | d ->
            let f = fold_mjoin (fun f -> 
                why3_and (pterm_of_fol f.value.value) (length_assert f.label.formula_data) 
            ) why3_or (term Ttrue) d.disjuncts
            in f::acc 
        ) inv spec.requires.conjuncts
    and sp_post =
      List.fold_left
        (fun l disj -> match disj with 
        | {disjuncts=[f]} -> 
                 (Loc.dummy_position,[pat Pwild , pterm_of_fol f.value.value]):: l 
        | d ->  
            let f = fold_mjoin (fun f -> pterm_of_fol f.value.value
            ) why3_or (term Ttrue) d.disjuncts
            in 
             (Loc.dummy_position,[pat Pwild ,f]) :: l 
          )
           (List.map (fun inv -> Loc.dummy_position,[pat Pwild , pterm_of_fol inv]) d.invariants)
        spec.ensures.conjuncts  |> List.rev
    in
    { empty_spec with sp_pre; sp_post }


  let generate_function (t: ((in_spec, out_body) hoare_triple, triple_data) labeled) =
    let open P in
    let open PH in
    let spec = generate_spec t.value.value t.label in
    Efun ([], None, pat Pwild, Ity.MaskVisible, spec, t.value.label) |> expr |> fun m ->
    Dlet (ident t.label.triple_id, false, Expr.RKnone, m)

  let generate_setup (s: in_setup) : out_setup  =
    let open P in
    let open PH in
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
      Efun ([], None, pat Pwild, Ity.MaskVisible, spec, bdy) |> expr |> fun m ->
      Dlet (ident "setup", false, Expr.RKnone, m)




  (** generates WhyML program expression to represent the setup procedure *)
  let generate_program p =
    let uses =
      [
        [ "int"; "Int" ];
        [ "int"; "EuclideanDivision" ];
        [ "ref"; "Ref" ];
        [ "list"; "List" ];
        [ "list"; "Length" ];
        [ "list"; "HdTlNoOpt" ];
        [ "list"; "NthNoOpt" ];
        [ "list"; "Quant" ];
        ["array"; "Init"]
      ]
      |> List.map (PH.use ~import:false)
    in
    let helper_m = (PH.ident "ProgramHelper", uses @ p.processed_decls) in
    let triples_m =
      ( PH.ident "Program",
        uses
        @ PH.use ~import:false [ "ProgramHelper" ]
          :: add_opt_to_list p.processed_setup p.processed_functions )
    in
    P.Modules [ helper_m; triples_m ]


  let write_program name p = print_program p (name ^ ".mlw")
end
