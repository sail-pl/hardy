(* open ArduinoSyntax.Locations *)
(* open ArduinoSyntax.Types *)
open ArduinoSyntax.Operators
open ArduinoSyntax.Fol
module S = ArduinoSyntax.Syntax
module AS = ArduinoSyntax.PromelaSyntax
open ArduinoSyntax.Locations
open Why3
open S
module H = Ptree_helpers
module P = Ptree

(* Should be moved with the definition of bform ? *)
let fol_of_bform (convert_atom : string -> expr fol) =
  let open AS in
  let rec aux = function
    | True -> mk_dummy_loc FOL_True
    | False -> mk_dummy_loc FOL_False
    | Atom s -> convert_atom s
    | And (s1, s2) ->
        let s1 = aux s1 in
        let s2 = aux s2 in
        mk_dummy_loc (FOL_Binary (s1, And, s2))
    | Or (s1, s2) ->
        let s1 = aux s1 in
        let s2 = aux s2 in
        mk_dummy_loc (FOL_Binary (s1, Or, s2))
    | Not s ->
        let s = aux s in
        mk_dummy_loc (FOL_Unary (Not, s))
  in

  aux

(* ok in file utils *)
(* Erase location to build a key *)
let rec determ_exp (e : expr) : expr =
  let value =
    match e.value with
    | BinOp (e1, op, e2) ->
        let e1 = determ_exp e1 and e2 = determ_exp e2 in
        BinOp (e1, op, e2)
    | _ as x -> x
  in
  { value; loc = None }

(* 2 formulas are equals if they are syntactically the same modulo their position *)
let rec determ_fol (f : expr fol) : expr fol =
  let value =
    match f.value with
    | Pred p -> Pred (determ_exp p)
    | FOL_Unary (op, f) ->
        let f = determ_fol f in
        FOL_Unary (op, f)
    | FOL_Binary (f1, op, f2) ->
        let f1 = determ_fol f1 and f2 = determ_fol f2 in
        FOL_Binary (f1, op, f2)
    | Forall (x, f) ->
        let f = determ_fol f in
        Forall (x, f)
    | Exists (x, f) ->
        let f = determ_fol f in
        Exists (x, f)
    | _ as x -> x
  in
  { value; loc = None }
