From Stdlib Require Import List.
From Hardy Require Import automaton.
Section Product.

    (** Given two automata [atm1 : automaton node1 label1] and 
        [atm2 : automaton node2 label2], we define their synchronized
        product as an automaton of type [automaton (node1*node2) (label1*label2)] *)

    Variable node1 node2 : Type.
    Variable label1 label2 : Type.

    Variable atm1 : automaton node1 label1.
    Variable atm2 : automaton node2 label2.

    Definition product : automaton (node1 * node2) (label1 * label2) :=
    {|
        init := (init atm1, init atm2);

        (** a valid transition of the product automaton ist just a merge 
            of a valid transition in the first automaton and in the second
        *)
        transition n l m :=
            transition atm1 (fst n) (fst l) (fst m) /\
            transition atm2 (snd n) (snd l) (snd m)
    |}.        

    (** We also define two projections over paths of the product automaton
        and state a few results relating paths in the product automaton 
        to their counterpart in the original automata *)

    Definition left_proj :
        list ((label1 * label2) * (node1 * node2)) -> list (label1 * node1) :=
            map (fun x => (fst (fst x), fst (snd x))).

    Definition right_proj :
        list ((label1 * label2) * (node1 * node2)) -> list (label2 * node2) :=
            map (fun x => (snd (fst x), snd (snd x))).

    Lemma fst_fst_left_proj :forall p,  map fst (map fst p) = map fst (left_proj p).
    Proof.
        induction p; cbn; [reflexivity| now rewrite IHp].
    Qed.        
    
    Lemma snd_fst_right_proj : forall p,  map snd (map fst p) = map fst (right_proj p).
    Proof.
        induction p; cbn; [reflexivity| now rewrite IHp].
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

    Section valid_lang.

        Variable Σ1 Σ2 Σ3 : Type.
        Variable sat_product : (label1 * label2) -> Σ3 -> Prop.
        Variable sat1 : label1 -> Σ1 -> Prop.
        Variable transf1 : Σ3 -> Σ1.
        Variable H1 : forall a b, sat_product a b -> sat1 (fst a) (transf1 b).


        Lemma valid_left_proj : 
            forall tr p, valid sat_product p tr -> 
                valid sat1 (List.map fst p) (List.map transf1 tr).
        Proof.
            induction tr as [|a tr IHtr]; 
                intros [|p] H_valid; inversion H_valid as [|? ? ? ? Hvsp Hsp]; subst; simpl.
            -   constructor. 
            -   apply IHtr in Hvsp. specialize (H1 _ _ Hsp). constructor ; assumption.
        Qed.

        Variable sat2 : label2 -> Σ2 -> Prop.
        Variable transf2 : Σ3 -> Σ2.
        Variable H2 : forall a b, sat_product a b -> sat2 (snd a) (transf2 b).

        Lemma valid_right_proj : 
            forall tr p, valid sat_product p tr -> 
                valid sat2 (List.map snd p) (List.map transf2 tr).
        Proof.
            induction tr as [|a tr IHtr]; 
                intros [|p] H_valid; inversion H_valid as [|? ? ? ? Hvsp Hsp]; subst; simpl.
            -   constructor. 
            -   apply IHtr in Hvsp. specialize (H2 _ _ Hsp). constructor ; assumption.
        Qed.

        Lemma language_left_proj : forall p w, language_wit sat_product product p w ->  
            language_wit sat1 atm1 (left_proj p) (List.map transf1 w).
        Proof.
            intros. inversion H. constructor.
            - now apply path_left_proj in H0.
            - apply valid_left_proj in H3. now rewrite <- fst_fst_left_proj. 
        Qed.

        Lemma language_right_proj : forall p w, language_wit sat_product product p w ->  
            language_wit sat2 atm2 (right_proj p) (List.map transf2 w).
        Proof.
            intros. inversion H. constructor.
            - now apply path_right_proj in H0.
            - apply valid_right_proj in H3.  now rewrite <- snd_fst_right_proj. 
        Qed.

    End valid_lang.


    Section Properties.
        Variable Σ1 Σ2 Σ3 : Type.
        Variable sat_product : (label1 * label2) -> Σ3 -> Prop.
        Variable sat1 : label1 -> Σ1 -> Prop.
        Variable transf1 : Σ3 -> Σ1.
        Variable H1 : forall a b, sat_product a b -> sat1 (fst a) (transf1 b).
        Variable sat2 : label2 -> Σ2 -> Prop.
        Variable transf2 : Σ3 -> Σ2.
        Variable H2 : forall a b, sat_product a b -> sat2 (snd a) (transf2 b).


        Lemma prod_complete : 
            aut_complete _ _ atm1 -> 
            aut_complete _ _ atm2 ->
            aut_complete _ _ product.
        Proof.
            intros * Ha Hb n H.
            assert (Hr1: reachable atm1 (fst n)).
            {
                destruct n.
                simpl.
                apply reachable_left_proj in H.
                apply H.
            }
            assert (Hr2: reachable atm2 (snd n)).
            {
                destruct n.
                apply reachable_right_proj in H.  
                apply H.
            }
            apply Ha in Hr1 as [f [n1 Hat]].
            apply Hb in Hr2 as [g [m1 Hbt]].
            exists (f,g), (n1,m1).
            split; assumption.
        Qed.


        Lemma prod_deterministic : 
            aut_deterministic _ _ _ sat1 atm1 ->
            aut_deterministic _ _ _ sat2 atm2 ->
            aut_deterministic _ _ _ sat_product product.
        Proof.
            intros Ha Hg. red. split.
            - intros [l l'] m [l1 l1'] m' s [Ht1 Hs1] [Ht2 Hs2]. destruct Ht1, Ht2.
            destruct Ha as [Ha _], Hg as [Hg _].
            apply H1 in Hs1 as Hs1a. apply H2 in Hs1 as Hs1g.
            apply H1 in Hs2 as Hs2a. apply H2 in Hs2 as Hs2g.

            pose proof (Ha _ _ _ _ _ (conj H Hs1a) (conj H3 Hs2a)).
            pose proof (Hg _ _ _ _ _ (conj H0 Hs1g) (conj H4 Hs2g)).
            destruct H5, H6. destruct m, m'. cbn in *. now subst.

            - intros s w. destruct w. 
                + intros. inversion H. inversion H5.
                + intros [[p1 p2] [p3 p4]] p [n1 n1'] [n2 n2'] [l1 l1'] [l2 l2'] Hw [Ht1 Ht2] [Ht'1]. 
                    apply language_left_proj with (transf1:=transf1) (sat1:=sat1) in Hw as Hw_left; [|assumption].
                    apply language_right_proj with (transf2:=transf2) (sat2:=sat2) in Hw as Hw_right; [|assumption].
                    destruct Ht1, Ht'1.
                    destruct Ha as [_ Ha], Hg as [_ Hg]. cbn in *.
                    apply H1 in Ht2 as Ht1. apply H2 in Ht2.
                    apply H1 in H as H'. apply H2 in H.

                    epose proof Ha _ _ _ _ _ _ _ _ Hw_left (conj H0 Ht1) (conj H4 H'). 
                    epose proof Hg _ _ _ _ _ _ _ _ Hw_right (conj H3 Ht2) (conj H5 H). destruct H6. destruct H7. now subst.
        Qed.

    End Properties.
End Product.

Arguments product [node1 node2 label1 label2].
Arguments left_proj [node1 node2 label1 label2].
Arguments right_proj [node1 node2 label1 label2].