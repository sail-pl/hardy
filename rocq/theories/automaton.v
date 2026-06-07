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

    Definition successors (atm : automaton) (n: node) (succs: Ensemble (label * node)) : Prop :=
         forall l m, In _ succs (l,m) <-> transition atm n l m
    .

    Definition predecessors (atm : automaton) (preds: Ensemble (node * label)) (m: node) : Prop := 
        forall l n, In _ preds (n,l) <-> reachable atm n /\ transition atm n l m
    .


    (* only the initial node is allowed not to have predecessors *)
    Hypothesis init_no_pred : 
         forall n atm , n <> init atm -> exists preds, predecessors atm preds  n /\ preds <> Empty_set _. 




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

End Automata.

Arguments init [node label].
Arguments transition [node label].
Arguments path [node label].
Arguments valid [label Σ].
Arguments language_wit [node label Σ].
Arguments language [node label Σ].
Arguments reachable_from [node label].
Arguments reachable [node label].

