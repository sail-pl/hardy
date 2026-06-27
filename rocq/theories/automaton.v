From Stdlib Require Import List Ensembles.

Section Automata.

    (** An automaton is charaterized by a collection of nodes (type [node]),
        labels (type [label]) and transitions. We distinguish an initial node
        ([init]). We consider automata where all nodes [node] are accepting. *)

    Variable node : Type.
    Variable label : Type.

    Record automaton  : Type := {
        init : node;
        transition : node -> label -> node -> Prop
    }.

    (** A path of the automaton [atm] starting at node [n] is a list
        of pairs of type [label * node] matching transitions of [atm]. *)

    Inductive path (atm : automaton) (n : node) : list (label * node) -> Prop :=
    | path_empty : path atm n nil
    | path_transition : forall lbl m,
        transition atm n lbl m -> 
        path atm n (cons (lbl,m) nil)
    | path_transitive : forall m0 m1 lbl0 lbl1 p,
        path atm n (cons (lbl0, m0) p) -> 
        transition atm m0 lbl1 m1 ->
        path atm n (cons (lbl1,m1) (cons (lbl0, m0) p)).

    Lemma path_prefix_closed : forall atm n x p, 
        path atm n (x::p) -> path atm n p.
    Proof.
        intros atm n x p xp_path.
        inversion xp_path; auto using path.
    Qed.    

    (** A node [m] is reachable from the node [n] in [atm] if either 
        n = m or there exists a path from n which ends in m *)

    Definition reachable_from (atm : automaton) (n m : node) : Prop :=
        n = m \/
        exists lbl p, path atm n (cons (lbl, m) p).

    Definition reachable (atm : automaton) (n : node) : Prop :=
        reachable_from atm (init atm) n.

    Definition successor := fun a m l n => transition a n l m.

    Definition predecessor := transition.


    (** Given a type [Σ] and a predicate [belongs : label -> Σ -> Prop], a finite word 
        w (a list) of elements of type [Σ] is valid for a path p if w and p have the same length
        and [belongs lbl a] for each lbl and a occuring at the same position in p and w
        respectively. *)

    Variable Σ : Type.
    Variable belongs : label -> Σ -> Prop.

    Inductive valid : list label -> list Σ ->  Prop :=
        | valid_nil : valid nil nil
        | valid_cons : forall a w lbl lbls,
            valid lbls w -> belongs lbl a ->
            valid (cons lbl lbls) (cons a w).

    Lemma valid_prefix_closed : forall lbl a l m,
        valid (cons lbl l) (cons a m) -> valid l m.
    Proof.
        intros lbl a l m H; now inversion H.
    Qed.
    
    (** A word w is in the language of the automaton [atm] if there exists 
        a path p such that w is valid with respect to p. *)

    Definition language (atm : automaton) : list Σ -> Prop :=
        fun w =>
            exists p, path atm (init atm) p /\ 
                valid (List.map fst p) w.
        

    (** For technical purpose, we consider an alternative definition of the
        language of automaton in which the path appears as a witness. *)

    Definition language_wit (atm : automaton) : list (label * node) -> list Σ -> Prop :=
        fun p w =>
            path atm (init atm) p /\ 
                valid (List.map fst p) w.
            

    Lemma language_empty : forall (atm : automaton), language_wit atm nil nil.
    Proof.
        split; constructor.
    Qed.

    Lemma language_w_nil : forall (aut : automaton) p,
    language_wit aut p nil -> p = nil.
    Proof.
        intros aut p H.
        destruct H as [_ H_valid].
        destruct p; [reflexivity| inversion H_valid].
    Qed.

    Lemma language_prefix_closed : forall aut h p a l, language_wit aut (h::p) (a::l) -> language_wit aut p l.
    Proof.
        intros aut h p a w [H_path H_valid].
        split.
        - now (inversion H_path; auto using path_empty).
        - now (inversion H_valid; trivial).
    Qed.



    Definition aut_complete (a: automaton): Prop := 
        forall n, reachable a n -> exists p m, transition a n p m.


    Definition aut_deterministic (a: automaton) :  Prop :=
       (forall l m l' m' s,
        transition a (init a) l m /\ belongs l s ->
        transition a (init a) l' m' /\ belongs l' s ->
        l = l' /\ m = m' 
       )
        /\
        (
        forall s w (x : label * node) p m m' l l', 
        language_wit a (x::p) w -> 
        transition a (snd x) l m /\ belongs l s ->
        transition a (snd x) l' m' /\ belongs l' s ->
        l = l' /\ m = m' )  
    .

    Lemma aut_deterministic_eq (a: automaton ):  
        aut_deterministic a -> 
        forall w p p', 
        language_wit a p w ->
        language_wit a p' w ->
        p = p'
    .
    Proof.
        induction w.
        - intros. apply language_w_nil in H0,H1. now subst.
        - intros. destruct p;[ now inversion H0|]; destruct p'; [now inversion H1|].
            apply language_prefix_closed in H0 as H0',H1 as H1'.
            specialize (IHw _ _ H0' H1'); subst. clear H1'. f_equal.
            inversion H0; inversion H1. destruct H.
            inversion H3; subst. inversion H5; subst. 
            inversion H2; subst.
            + inversion H4. subst.
                specialize (H _ _ _ _ _ (conj H8 H12) (conj H9 H14)). inversion H. now subst.
            + inversion H4; subst.
                (* assert (language_wit a ((lbl0, m0) :: p0) w ) by auto. *)
                epose proof (H6 _ _ _ _ _ _ _ _ H0' (conj H13 H12) (conj H18 H14)). inversion H7. now subst.
    Qed.

End Automata.

Arguments init [node label].
Arguments transition [node label].
Arguments path [node label].
Arguments valid [label Σ].
Arguments language_wit [node label Σ].
Arguments language [node label Σ].
Arguments reachable_from [node label].
Arguments reachable [node label].

