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
  | Prod of 't expr list
  | Array of 't expr list
  | Not of 't expr
  | BinOp of { left : 't expr; op : arithm_binop; right : 't expr }
  | ArrayCell of { array : 't expr; idx : 't expr }

(** [private_var x] renames variable id [x] to a name that cannot have been
    declared by the user *)
let private_var = String.cat "_"

let rec fold_expr : type a. ('t expr -> a -> a) -> 't expr -> a -> a =
 fun j e init ->
  match e.value with
  | Int _ | True | False | Var _ | Not _ | String _ -> j e init
  | ArrayCell v -> j e (fold_expr j v.idx init)
  | BinOp v -> j e (fold_expr j v.right (fold_expr j v.left init))
  | Array arr | Prod arr -> List.fold_right (fold_expr j) arr init

let rec map_expr : ('t expr -> 't expr) -> 't expr -> 't expr =
 fun m e ->
  match e.value with
  | Int _ | True | False | Var _ | Not _ | String _ -> m e
  | ArrayCell v ->
      m
        {
          e with
          value =
            ArrayCell { idx = map_expr m v.idx; array = map_expr m v.array };
        }
  | BinOp v ->
      m
        {
          e with
          value =
            BinOp
              { v with left = map_expr m v.left; right = map_expr m v.right };
        }
  | Array arr -> m { e with value = Array (List.map (map_expr m) arr) }
  | Prod l -> m { e with value = Prod (List.map (map_expr m) l) }

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
  | Emit of 't expr * string
  | Clear of 't expr (* set a variable to Nil  (not for outputs) *)
  | If of 't expr * ('inv, 't) stmt list * ('inv, 't) stmt list option
  | When of string * ('inv, 't) stmt list * ('inv, 't) stmt list option
  | While of 't expr * 'inv * unit expr * ('inv, 't) stmt list

type 'ty var_decls = (string * 'ty) list

type ('inst_spec, 't) node = {
  node_id : string;
  node_variables : base_ty var_decls;
  node_preamble : ('inst_spec, unit) stmt list;
  node_spec : 'inst_spec list hoare_pair;
  node_transitions :
    (unit expr option * ('inst_spec, unit) stmt list * string option) list;
}

let init_node = "START"
let find_node l id = List.find (fun n -> n.node_id = id) l
let find_start_node l = find_node l init_node

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
