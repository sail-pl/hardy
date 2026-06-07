(* tried to define an inductive invariant as with lamport's paper but don't know if relevant *)

    (* Inductive IC (n:node1*node2) : Prop := 
    | Init: 
        init io_aut = n ->
        (exists fg m, 
        transition io_aut n fg m /\
        (forall i st, P_init st -> 
        (fst fg) (nil,i) -> 
        (snd fg) (nil,(i,program (i,st))))) ->
        IC n
    | Next prev_n (prev_fg: i_p_type* o_p_type): 
        IC prev_n ->
        (exists fg m, 
        transition io_aut n fg m ->
        (forall prev_i i st h, 
            (snd prev_fg) (h,(prev_i,st)) ->
            (fst fg) ((prev_i,st)::h,i) ->
            (snd fg) (((prev_i,st)::h), (i,program (i,st))) 
        )) ->
        IC n
    .


    Goal validAutomaton <-> (forall q,  reachable io_aut q -> 
    IC q).
    Proof.
        split.
        - intros [init H]. intros q. specialize (H q). intro H1. pose proof H1 as H2. specialize (H H1). induction H1.
        (* init node *)
            + clear H. subst. destruct (io_aut_successor (automaton.init io_aut) H2) as [[f g] [m Haut]].  econstructor 1.
                * easy.
                * exists (f,g),m. split. 
                    ** easy.
                    **  intros. simpl in *.  specialize (init f i st). destruct init; auto.
                    ++ now exists g,m.
                    ++ destruct H1. destruct H1. destruct H1. simpl in *. destruct Haut. replace x with g in H3. unfold transition in H1. auto. admit.
                    (* next node *)
            + destruct H0. destruct H0. econstructor 2.
                * admit.
                * admit.
        - intros. unfold validAutomaton. split.
            + red. intros. destruct H0 as [g [q Htr]]. specialize H with q.
                assert(reachable io_aut q). {
                    constructor 2. eexists. eexists. constructor. apply Htr. 
                }
                specialize (H H0). inversion H.
                * subst. destruct H4. destruct H3. destruct H3. exists g,(init io_aut). split; auto.
                    specialize (H4 i st H1). admit.
                *
           + *)



(* 
    Proposition correctness_aux2 : 
    forall (m0 : state) (tr : trace), 
        (forall q fg q', IC q fg q') -> 
        D.P_init m0 -> run m0 tr -> 
        forall (ip:i_path_type), language_wit sat_i i_aut ip (build_trace_history tr) ->
        exists (p:io_path_type), 
        left_proj p = ip /\ language_wit sat_product io_aut p (build_trace_history tr).
   Proof.
    intros o_start tr Hic o_start_valid run.
        induction run as 
            [ o_start | i0 o_start |  
                o_start i_k o_k i_Sk o_Sk tr run tr_lang step ]; 
        intros ipath input_lang.

        -   replace ipath with (nil : list (i_p_type * node1)) by
                now rewrite (language_w_nil _ _ _ _ _ _ input_lang).
            exists nil.
            split; [reflexivity | apply language_empty].

        -   destruct input_lang as [H_path H_valid].
            (** that the word [i0] is valid implies [is] is directly a transition from 
                the initial node to [n1] labeled [f] such that [f] satisfies [i0].
            *)
            destruct ipath as [ | [f n1] ipath]; [ inversion H_valid |]. 
            destruct ipath as [ | ]; inversion_clear H_valid as [ | ? ? ? ? [|] input_hd_is_valid]. 

            assert (h_transition : transition i_aut (init i_aut) f n1) by now (inversion H_path; subst).


            (** there must exist a transition in the product automaton from its initial node
                to [(n1,m)] for a certain [m] labeled with [(f,g)] such that given 
                the initial output [i0], the new state produced by the system is correct (g holds)  
            *)
            assert (exists g m, 
                transition io_aut (init i_aut, init o_aut) (f,g) (n1, m) /\ 
                    g (nil, (i0, program (i0, o_start)))) as [g [m [Hu Hw]]].
            {

            assert (Hy : exists (g : o_p_type) (m : node1*node2),
                                transition io_aut (init io_aut) (f, g) m).
                    {
                        assert (reachable o_aut (init o_aut)) as H_reach by (left; reflexivity).
                        destruct (o_aut_successor (init o_aut) H_reach) as [g [m H_trans]].
                        exists g, (n1, m); easy.
                    }
                    destruct Hy as [g [m H]]. 
                specialize (Hic (automaton.init io_aut) (f,g) m). inversion Hic.
                - subst. simpl in *. specialize (H2 i0 o_start o_start_valid). exists g,(snd m). destruct H. repeat (split; auto). 
                -  admit.
            }

            exists (((f,g), (n1,m))::nil).
            split; [reflexivity|].
            split.
            +   exact (path_transition _ _ _ _ _ _ Hu). 
            +   assert (sat_product (f, g) (nil, (i0, program (i0, o_start)))) as H_sat
                    by (exact (conj input_hd_is_valid Hw)).
                exact (valid_cons _ _ _ _ _ _ _ (valid_nil _ _ _) H_sat).
    - admit.
   Qed. *)
