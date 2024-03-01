Require Import automata.automaton.
Require Import List.

Section Product.

    (** Given two automata [atm1 : automaton node1 label1] and 
        [atm2 : automaton node2 label2], we defined their synchronized
        product as an automaton of type [automaton (node1*node2) (label1*label2)] *)

    Variable node1 node2 : Type.
    Variable label1 label2 : Type.

    Variable atm1 : automaton node1 label1.
    Variable atm2 : automaton node2 label2.

    Definition product : automaton (node1 * node2) (label1 * label2) :=
    {|
        init := (init atm1, init atm2);
        transition n l m :=
            transition atm1 (fst n) (fst l) (fst m) /\
            transition atm2 (snd n) (snd l) (snd m)
    |}.        

    (** We also define two projections other paths of the product automaton
        and state a few results relating paths in the product automaton 
        and their counterpart in the original automata *)

    Definition left_proj :
        list ((label1 * label2) * (node1 * node2)) -> list (label1 * node1) :=
            map (fun x => (fst (fst x), fst (snd x))).

    Definition right_proj :
        list ((label1 * label2) * (node1 * node2)) -> list (label2 * node2) :=
            map (fun x => (snd (fst x), snd (snd x))).

    Lemma temp0 : forall io_p,
        map snd (map fst io_p) = map fst (right_proj io_p).
    Proof.
        induction io_p.
        reflexivity.
        simpl.
        f_equal.
        apply IHio_p.
    Qed.
    

    Lemma path_left_proj : 
        forall n p, path product n p ->
            path atm1 (fst n) (left_proj p).
    Proof.
        induction p; intro H_produce.
        -   constructor.
        -   inversion H_produce; subst.
            +   constructor.
                apply H0.
            +   apply IHp in H1.
                constructor.
                apply H1.
                apply H2.
    Qed.

    Lemma path_right_proj : 
        forall n p, path product n p ->
            path atm2 (snd n) (right_proj p).
    Proof.
        induction p; intro H_produce.
        -   constructor.
        -   inversion H_produce; subst.
            +   constructor.
                apply H0.
            +   apply IHp in H1.
                constructor.
                apply H1.
                apply H2.
    Qed.

    Lemma reachable_left_proj : 
        forall n m, reachable_from product n m -> 
            reachable_from atm1 (fst n) (fst m).
    Proof.
        intros [n1 n2] [m1 m2] H_reachable.
        destruct H_reachable as [H_start | H_reach_trans].
        -   left.
            congruence.
        -   right.
            destruct H_reach_trans as [ [lbl1 lbl2] [p H_path_product]].
            exists lbl1, (left_proj p).
            apply path_left_proj in H_path_product.
            apply H_path_product.
    Qed.

    Lemma reachable_right_proj : 
        forall n m, reachable_from product n m -> 
            reachable_from atm2 (snd n) (snd m).
    Proof.
        intros [n1 n2] [m1 m2] H_reachable.
        destruct H_reachable as [H_start | H_reach_trans].
        -   left.
            congruence.
        -   right.
            destruct H_reach_trans as [ [lbl1 lbl2] [p H_path_product]].
            exists lbl2, (right_proj p).
            apply path_right_proj in H_path_product.
            apply H_path_product.
    Qed.

    Section valid_proj.

        Variable alph2 alph3 : Type.
        Variable sat_product : (label1 * label2) -> alph3 -> Prop.
        Variable sat : label2 -> alph2 -> Prop.
        Variable transf : alph3 -> alph2.
        Variable H : forall a b, sat_product a b -> sat (snd a) (transf b).

        Lemma valid_right_proj : 
            forall tr p, valid sat_product p tr -> 
                valid sat (List.map snd p) (List.map transf tr).
        Proof.
            induction tr.
            -   intros p H_valid.
                destruct p.
                +   simpl.
                    constructor.
                +   inversion H_valid.
            -   intros p H_valid.
                destruct p.
                +   inversion H_valid.
                +   inversion H_valid.
                    subst.
                    apply IHtr in H3.
                    constructor.
                    apply H3.
                    apply H.
                    apply H5.
        Qed.

    End valid_proj.

    Definition sat_product {A B} := 
        fun (p : (A -> Prop) * ((A* B) -> Prop)) (x : A * B) => 
            ((fst p) (fst x) /\ (snd p) x).

End Product.

Arguments product [node1 node2 label1 label2].
Arguments left_proj [node1 node2 label1 label2].
Arguments right_proj [node1 node2 label1 label2].
