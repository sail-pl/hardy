Require Import List.

Lemma map_id : forall (A : Type) (l : list A), map id l = l.
Proof.
    induction l as [ | ? ? IHl]; [reflexivity| simpl; f_equal; exact IHl].
Qed.




Fixpoint map2 {A B C : Type} (f : A -> B -> C) (l1:list A) (l2 :list B) : list C :=
match l1,l2 with
    | nil,nil => nil
    | cons a t,cons b t' => cons (f a b) (map2 f t t')
    | _,_ => nil
end.