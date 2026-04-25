open HardyMisc.Utils
open SharedSyntax


type pltl_unary =
  | PLTL_StdUnary of standard_logic_uop
  | Once
  | Yesterday
  | WeakYesterday
  | Historically

type pltl_binary = 
  | PLTL_StdBinary of standard_logic_bop 
  | Since
  | WeakSince

type 'a pltl = 'a pltl_ locatable

and 'a pltl_ =
  | PLTL_True
  | PLTL_False
  | PLTL_Atom of 'a 
  | PLTL_Unary of pltl_unary * 'a pltl
  | PLTL_Binary of 'a pltl * pltl_binary * 'a pltl


let rec fold_pltl (j: 'acc -> 'a pltl -> 'acc) (pj : 'acc -> 'a -> 'acc)  (init: 'acc) (form: 'a pltl)  = match form.value with
| PLTL_True | PLTL_False -> j init form 
| PLTL_Atom p -> pj init p 
| PLTL_Unary (_,f')  -> j (fold_pltl j pj init f') form 
| PLTL_Binary (f1,_, f2) -> j (fold_pltl j pj (fold_pltl j pj init f1) f2) form 


let rec map_pltl_pred : type a b. (a -> b) -> a pltl -> b pltl =
 fun m form ->
  match form.value with
  | PLTL_Atom p ->
      let value = PLTL_Atom (m p) in
      { form with value }
  | PLTL_Unary (un, f') ->
      let value = PLTL_Unary (un, map_pltl_pred m f') in
      { form with value }
  | PLTL_Binary (f'1, bin, f'2) ->
      let value = PLTL_Binary (map_pltl_pred m f'1, bin, map_pltl_pred m f'2) in
      { form with value }
  | (PLTL_True | PLTL_False) as value -> { form with value }


let atom_pltl a = mk_dummy_loc (PLTL_Atom a)
let and_pltl (f1 : 'a pltl) (f2 : 'a pltl) : 'a pltl =
  mk_dummy_loc (PLTL_Binary (f1, PLTL_StdBinary LAnd, f2))

let or_pltl (f1 : 'a pltl) (f2 : 'a pltl) : 'a pltl =
  mk_dummy_loc (PLTL_Binary (f1, PLTL_StdBinary LOr, f2))

let not_pltl (f : 'a pltl) : 'a pltl =
  mk_dummy_loc (PLTL_Unary (PLTL_StdUnary LNot ,f))

let true_pltl = mk_dummy_loc PLTL_True
let false_pltl = mk_dummy_loc PLTL_True

let pltl_of_bool_a (convert_atom : 'a -> 'b pltl) (f: 'a bool_a) : 'b pltl =
    let rec aux = function
    | True -> true_pltl
    | False -> false_pltl
    | Atom a -> convert_atom a
    | And (f1, f2) -> and_pltl (aux f1) (aux f2) 
    | Or (f1,f2) -> or_pltl (aux f1) (aux f2)
    | Not f -> not_pltl (aux f)
in aux f
