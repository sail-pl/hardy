(** {1 Terms for (Propositional) Linear Temporal Logic} *)

type ltl_unary =
    LTL_StdUnary of SharedSyntax.standard_logic_uop
    | Next
    | Always
    | Eventually
type ltl_binary =
    LTL_StdBinary of SharedSyntax.standard_logic_bop
    | Until
    | WeakUntil
    | Release
    | StrongRelease

(** Linear Temporal Logic formulas parameterized by predicates *)
type 'a ltl = 'a ltl_ HardyMisc.Utils.locatable
and 'a ltl_ =
    LTL_True
    | LTL_False
    | LTL_Atom of 'a
    | LTL_Unary of ltl_unary * 'a ltl
    | LTL_Binary of 'a ltl * ltl_binary * 'a ltl


val fold_ltl : ('acc -> 'a ltl -> 'acc) -> ('acc -> 'a -> 'acc) -> 'acc -> 'a ltl -> 'acc

(** [map_ltl_pred m f] applies [m] to every predicates making up the formula [f]*)
val map_ltl_pred : ('a -> 'b) -> 'a ltl -> 'b ltl


(** {2 Helpers to build locatable formulas} *)

val and_ltl : 'a ltl -> 'a ltl -> 'a ltl

val disj_ltl : 'a ltl -> 'a ltl -> 'a ltl

val true_ltl : ('a ltl_, 'b option) HardyMisc.Utils.labeled

val false_ltl : ('a ltl_, 'b option) HardyMisc.Utils.labeled

val not_ltl : 'a ltl -> ('a ltl_, 'b option) HardyMisc.Utils.labeled

val atom_ltl : 'a -> ('a ltl_, 'b option) HardyMisc.Utils.labeled
