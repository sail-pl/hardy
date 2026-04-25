type pltl_unary =
    PLTL_StdUnary of SharedSyntax.standard_logic_uop
  | Once
  | Yesterday
  | WeakYesterday
  | Historically

type pltl_binary =
    PLTL_StdBinary of SharedSyntax.standard_logic_bop
  | Since
  | WeakSince

type 'a pltl = 'a pltl_ HardyMisc.Utils.locatable
and 'a pltl_ =
    PLTL_True
  | PLTL_False
  | PLTL_Atom of 'a
  | PLTL_Unary of pltl_unary * 'a pltl
  | PLTL_Binary of 'a pltl * pltl_binary * 'a pltl

val fold_pltl :
  ('acc -> 'a pltl -> 'acc) ->
  ('acc -> 'a -> 'acc) -> 'acc -> 'a pltl -> 'acc

(** [map_ltl_pred m f] applies [m] to every predicates making up the formula [f]*)
val map_pltl_pred : ('a -> 'b) -> 'a pltl -> 'b pltl


(** {2 Helpers to build locatable formulas} *)

val atom_pltl : 'a -> ('a pltl_, 'b option) HardyMisc.Utils.labeled

val and_pltl : 'a pltl -> 'a pltl -> 'a pltl

val or_pltl : 'a pltl -> 'a pltl -> 'a pltl

val not_pltl : 'a pltl -> 'a pltl

val true_pltl : ('a pltl_, 'b option) HardyMisc.Utils.labeled

val false_pltl : ('a pltl_, 'b option) HardyMisc.Utils.labeled

val pltl_of_bool_a : ('a -> 'b pltl) -> 'a SharedSyntax.bool_a -> 'b pltl
