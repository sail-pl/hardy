(** Program Syntax *)

open HardyMisc.Utils
open SharedSyntax

(* Expressions *)

type 't expr = 't expression_ locatable
(** variables can carry extra information of type ['t] *)

and 't expression_ =
  | Int of int
  | True
  | False
  | String of string
  | Var of string * 't
  | Read of string
  | Array of 't expr list
  | Not of 't expr
  | BinOp of 't expr * arithm_binop * 't expr
  | ArrayCell of 't expr * 't expr

(** [private_var x] renames variable id [x] to a name that cannot have been
    declared by the user *)
let private_var = String.cat "_"

let rec fold_expr : type a. ('t expr -> a -> a) -> 't expr -> a -> a =
 fun j e init ->
  match e.value with
  | Int _ | True | False | Var _ | Read _ | Not _ | String _ -> j e init
  | ArrayCell (_,e') -> j e (fold_expr j e' init)
  | BinOp (e1, _, e2) -> j e (fold_expr j e2 (fold_expr j e1 init))
  | Array arr -> List.fold_right (fold_expr j) arr init

let rec map_expr : ('t expr -> 't expr) -> 't expr -> 't expr =
 fun m e ->
  match e.value with
  | Int _ | True | False | Var _ | Read _ | Not _ | String _ -> m e
| ArrayCell (id,e') -> m { e with value = ArrayCell (id,map_expr m e') }
  | BinOp (e1, op, e2) ->
      m { e with value = BinOp (map_expr m e1, op, map_expr m e2) }
  | Array arr -> m { e with value = Array (List.map (map_expr m) arr) }

let expr_vars (e : 't expr) : (string * 't) list -> (string * 't) list =
  fold_expr
    (fun e l -> match e.value with Var (x, t) -> (x, t) :: l | _ -> l)
    e

type 'spec hoare_pair = { requires : 'spec; ensures : 'spec }
(** generic hoare requires/ensures pair *)

type ('a, 'spec) hoare_triple = 'a * 'spec hoare_pair
type 'v variant = { variant : 'v }

let mk_variant x : _ variant = { variant = x }
let variant x = x.variant

type ('inv, 't) stmt = ('inv, 't) stmt_ locatable
(** program statements *)

and ('inv, 't) stmt_ =
  | Assign of 't expr * 't expr
  | Emit of 't expr option * string
  | Clear of 't expr
  | If of
      't expr * ('inv, 't) stmt list * ('inv, 't) stmt list option
  | While of 't expr * 'inv * unit expr * ('inv,'t) stmt list



type 'ty var_decls = (string * 'ty) list

type ('inst_spec, 't) node = {
  node_id : string;
  node_variables : base_ty var_decls;
  node_spec : 'inst_spec list hoare_pair;
  node_body : ('inst_spec,unit) stmt list;
  node_transitions : (unit expr option * string) list ;
}

let init_node = "START"

let find_node id l = List.find (fun n -> n.node_id = id) l

let find_start_node l = find_node init_node l

type 'ty env = {
  env_input : 'ty var_decls;
  env_output : 'ty var_decls;
  env_variables : 'ty var_decls;
}
(** program memory environment *)

type ('temp_spec, 'inst_spec, 't) program = {
  prog_decls : base_ty env;
  prog_spec : 'temp_spec list hoare_pair;
  prog_nodes : ('inst_spec, 't) node list;
}
