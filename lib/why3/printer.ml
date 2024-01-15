open Syntax 

let comma out () = Format.fprintf out ", "
let br out () = Format.fprintf out "\n"


let rec pp_pty out (p : pty) = 
  match p with 
    | PTtyapp (x, l) -> Format.fprintf out "(%a) %s " (Format.pp_print_list ~pp_sep:comma pp_pty) l x
    | PTref p -> Format.fprintf out "%a ref" pp_pty p

let pp_true out = 
  Format.pp_print_string out "true"

let pp_false out = 
  Format.pp_print_string out "false"

let pp_unit out = 
  Format.pp_print_string out "()"
  
let pp_const out (c : constant) = 
  match c with 
  | None -> pp_unit out
  | Some n -> Format.pp_print_int out n

let pp_binder out b =  
  Format.fprintf out "%a : %a" 
    (Format.pp_print_list Format.pp_print_string) (fst b)
    pp_pty (snd b)

  let pp_binder2 out b =  
    Format.fprintf out "(%a : %a)" 
      (Format.pp_print_list Format.pp_print_string) (fst b)
      pp_pty (snd b)

 let rec pp_term out (t : term) = 
  match t with 
    | Ttrue -> Format.pp_print_string out "true"
    | Tfalse -> Format.pp_print_string out "false"
    | Tconst c -> pp_const out c
    | Tident x -> Format.pp_print_string out x
    | Tidapp (x, l) -> 
      Format.fprintf out "%s (%a)" x 
        (Format.pp_print_list ~pp_sep:comma pp_term) l
    | Tapply(t1,t2) -> 
        Format.fprintf out "%a %a" pp_term t1 pp_term t2 
    | Tinfix(t1,o,t2) -> 
      Format.fprintf out "%a %s %a" pp_term t1 o pp_term t2
    | TAnd (t1, t2) -> 
      Format.fprintf out "%a /\\ %a" pp_term t1 pp_term t2
    | TOr (t1, t2) -> 
      Format.fprintf out "%a \\/ %a" pp_term t1 pp_term t2
    | TImp (t1, t2) -> 
        Format.fprintf out "%a -> %a" pp_term t1 pp_term t2
    | Tnot (t) -> 
        Format.fprintf out "not (%a)" pp_term t
    | TForall (l, t) -> 
        Format.fprintf out "forall %a, %a" 
          (Format.pp_print_list ~pp_sep:comma pp_binder) l 
          pp_term t
    | TExists (l, t) -> 
      Format.fprintf out "forall %a, %a" 
        (Format.pp_print_list ~pp_sep:comma pp_binder) l 
        pp_term t

        (* type expr = 
	| Etrue
  | Efalse
  | Econst of constant 
  | Eident of qualid
  | Eapply of expr * expr 
  | Einfix of expr * ident * expr 
  | Elet of ident * expr * expr 
  | Erecord of (qualid * expr) list 
  | Eassign of expr * qualid option * expr  
  | Esequence of expr * expr 
  | Eif of expr * expr * expr 
  | EWhile of expr * invariant * variant * expr 
  | Eand of expr * expr 
  | Eor of expr * expr 
  | Enot of expr 
  | Eassert of term  *)

  let pp_invariant out (i : term) = 
    Format.fprintf out "invariant {%a}" pp_term i

  let pp_variant out (i : term) = 
      Format.fprintf out "variant [%a]" pp_term i
  
  let pp_requires out (t : term) = 
    Format.fprintf out "requires {%a}" pp_term t

  let pp_ensures out (t : term) = 
    Format.fprintf out "ensures {%a}" pp_term t
    
  let pp_spec out (p : spec) = 
    Format.fprintf out "%a\n%a\n" pp_requires p.sp_pre pp_ensures p.sp_post

  let rec pp_expr out (e : expr) = 
    match e with 
      | Etrue -> pp_true out
      | Efalse -> pp_false out
      | Econst c -> pp_const out c
      | Eident x -> Format.pp_print_string out x
      | Eapply (e1, e2) -> Format.fprintf out "%a %a" pp_expr e1 pp_expr e2
      | Einfix (e1,o,e2) -> Format.fprintf out "%a %S %a" pp_expr e1 o pp_expr e2
      | Elet (x,e1,e2) -> 
        Format.fprintf out "let %s = %a in\n%a" x pp_expr e1 pp_expr e2
      | Erecord _l -> Format.fprintf out "record"
      | Eassign (e1,f,e2) -> 
          begin match f with 
            | None -> Format.fprintf out "%a := %a" pp_expr e1 pp_expr e2
            | Some _f -> failwith "unsupported record"
          end
      | Esequence (e1, e2) -> 
          Format.fprintf out "%a;\n%a" pp_expr e1 pp_expr e2
      | Eif (e1, e2, e3) -> 
        Format.fprintf out "if %a then\n%a\n else\n%a" pp_expr e1 pp_expr e2 pp_expr e3
      | EWhile (e1, i, v, e2) -> 
        Format.fprintf out "while %a do;\n %a \n %a \n%a\n done" 
          pp_expr e1 
            (Format.pp_print_list ~pp_sep:br pp_invariant) i 
            (Format.pp_print_list ~pp_sep:br pp_variant) v 
            pp_expr e2
      | Eand (e1, e2) -> 
        Format.fprintf out "%a && %a" pp_expr e1 pp_expr e2
      | Eor (e1, e2) -> 
        Format.fprintf out "%a || %a" pp_expr e1 pp_expr e2
      |Enot (e) ->
        Format.fprintf out "not (%a)" pp_expr e
      |Eassert (t) ->
          Format.fprintf out "assert {%a}" pp_term t


          (* type fundef = ident * binder list * spec * expr  *)

let pp_fun_def out (d : fundef) = 
  Format.fprintf out "%s %a %a %a" 
    d.fun_id   
    (Format.pp_print_list  pp_binder2) d.fun_params
    pp_spec d.fun_spec
    pp_expr d.fun_body
    

    let pp_module out (m : why3module) = 
      Format.fprintf out "%a" 
        (Format.pp_print_list pp_fun_def) m.m_rec
        
    (* type why3module = 
  {
    m_types : type_decl list;
    m_logic : logic_decl list;
    m_let : (ident * expr) list;
    m_rec : fundef list
  } *)
  