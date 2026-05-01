
open HardyMisc.Utils
open SharedSyntax

type ('a, 'qty) fol = ('a, 'qty) fol_ locatable

and ('a, 'qty) fol_ =
  | FOL_True
  | FOL_False
  | FOL_Atom of 'a
  | FOL_StdUnary of standard_logic_uop * ('a, 'qty) fol
  | FOL_StdBinary of ('a, 'qty) fol * standard_logic_bop * ('a, 'qty) fol
  
  (* convention: 
    LAnd [] <=> LOr []  <=> True 
  *)
  | FOL_StdNary of standard_logic_bop * ('a, 'qty) fol list  
  | Forall of (string * 'qty) list * ('a, 'qty) fol
  | Exists of (string * 'qty) list * ('a, 'qty) fol
  | ForallPrev of  ('a, 'qty) prev_quant
  | ExistsPrev of('a, 'qty) prev_quant 

and ('a, 'qty) prev_quant = {h_var: string; binder: string; f:  ('a, 'qty) fol}


type 'a predicate = Atom of 'a | Predicate of {name: string; args: 'a list}

let map_pred m : 'a predicate -> 'b predicate = function
  | Atom x -> Atom (m x)
  | Predicate x -> 
      let args = List.map m x.args in
      Predicate {x with args}
  

type ('a, 'qty) pred_fol = ('a predicate, 'qty) fol


type 'qty pred_decl = {name: string; params: string list; body: (string,'qty) fol }

let map_fol : type a b ty_a ty_b.
    ((a, ty_a) fol -> (b, ty_b) fol) ->
    (a -> b) ->
    (string * ty_a -> string * ty_b) ->
    (a, ty_a) fol ->
    (b, ty_b) fol =
 fun m m_atom m_ty form ->
  match form.value with
  | FOL_True | FOL_False as value-> {form with value}
  | FOL_Atom a -> {form with value=FOL_Atom (m_atom a)}
  | FOL_StdUnary (o, f) ->
      let value = FOL_StdUnary (o, m f) in
      { form with value }
  | FOL_StdBinary (f1, o, f2) ->
      let value = FOL_StdBinary (m f1, o, m f2) in
      { form with value }
  | FOL_StdNary (o,l) ->
      let value = FOL_StdNary (o, List.map m l) in
      { form with value }
  | Forall (l, f) ->
      let value = Forall (List.map m_ty l, m f) in
      { form with value }
  | Exists (l, f) ->
      let value = Exists (List.map m_ty l, m f) in
      { form with value }
  | ForallPrev q ->
      let f = m q.f in
      let value = ForallPrev {q with f} in
      { form with value }
  | ExistsPrev q ->
      let f = m q.f in
      let value = ExistsPrev {q with f} in
      { form with value }

let rec fold_fol : type a b t.
    (b -> (a, t) fol  -> b) -> (b -> a -> b) -> b -> (a, t) fol -> b =
 fun j pj init form ->
  match form.value with
  | FOL_True | FOL_False -> j init form 
  | FOL_Atom p -> pj init p 
  | FOL_StdUnary (_, f) -> j (fold_fol j pj init f) form
  | FOL_StdBinary (f1, _, f2) -> j (fold_fol j pj (fold_fol j pj init f1) f2) form
  | FOL_StdNary (_,l) -> j (List.fold_left (fold_fol j pj) init l) form
  | Forall (_, f) | Exists (_, f) -> j (fold_fol j pj init f) form
  | ExistsPrev q | ForallPrev q -> j (fold_fol j pj init q.f) form


let rec map_fol_ty m = map_fol (map_fol_ty m) Fun.id m


let map_fol_pred_ty (type a b ty_a ty_b) 
  (fty : ty_a -> ty_b)  (m : a -> b) 
  = let rec aux (f: (a predicate, ty_a) fol) : (b predicate, ty_b) fol =
    map_fol aux (map_pred m) (pair_map (Right fty)) f in aux  


let map_fol_pred = fun x -> map_fol_pred_ty (Fun.id) x


let true_fol : ('a, 'b) fol = mk_dummy_loc FOL_True
let false_fol : ('a, 'b) fol = mk_dummy_loc FOL_False
let atom_fol (x : 'a) : ('a, 'b) fol = mk_dummy_loc (FOL_Atom x)

let not_fol (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdUnary (LNot, f))

let and_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdBinary (f1, (LAnd), f2))

let or_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdBinary (f1, LOr, f2))

let equiv_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdBinary (f1, Equiv, f2))

let arrow_fol (f1 : ('a, 'b) fol) (f2 : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (FOL_StdBinary (f1, Arrow, f2))

let forall_fol (vars : (string * 'qty) list) (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (Forall (vars, f))

let exists_fol (vars : (string * 'qty) list) (f : ('a, 'b) fol) : ('a, 'b) fol =
  mk_dummy_loc (Exists (vars, f))

let fol_of_bool_a (convert_atom : 'a -> ('b, 'c) fol) (f: 'a bool_a) : ('b, 'c) fol =
  let rec aux = function
  | True -> true_fol
  | False -> false_fol
  | Atom a -> convert_atom a
  | And (f1, f2) -> and_fol (aux f1) (aux f2) 
  | Or (f1,f2) -> or_fol (aux f1) (aux f2)
  | Not f -> not_fol (aux f)
in aux f

let fol_of_cnf (convert_atom : 'a -> ('a, 'b) fol) (f: 'a cnf) : ('a, 'b) fol cnf =
  List.map (fun {disjuncts} ->
      List.map convert_atom disjuncts |> mk_disj
    ) f.conjuncts |> mk_conj