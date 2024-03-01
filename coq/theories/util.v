Require Import List.

Lemma map_id : forall (A : Type) (l : list A), map id l = l.
Proof.
    induction l as [ | ? ? IHl]; [reflexivity| simpl; f_equal; exact IHl].
Qed.
