Require Import List.
From Hardy Require Import automaton product util.

Module Type Verif_Domain.

    (** We assume two abstract types [input] and [state] denoting 
        inputs and states of the system. A program is a function
        mapping pairs of inputs and states to states.
        -   The predicate [P_init] describes the inital state of the system
        -   The bucchi automaton [i_aut] describes the input of the system.
        -   The bucchi automaton [o_aut] describes the expected state of 
            the system 
        We assume that in both automata, each node has at least a sucessor *)
 
    Parameter input state : Set.

    Parameter program : input * state -> state.

    Parameter P_init : state -> Prop.

    Parameter node1 node2 : Set.

    Parameter i_aut : automaton node1 (input -> Prop).
    Parameter o_aut : automaton node2 (input * state -> Prop).

    Parameter i_aut_successors : 
        forall n, reachable i_aut n -> 
            exists g m, transition i_aut n g m.

    Parameter o_aut_successors : 
        forall n, reachable o_aut n -> 
            exists g m, transition o_aut n g m.

    Notation i_step_type := ((input -> Prop) * node1).
    Notation o_step_type := ((input * state -> Prop) * node2).
    Notation i_path_type := (list i_step_type).
    Notation o_path_type := (list o_step_type).

End Verif_Domain.
                    
Module Verif (Import D : Verif_Domain).

    (** The function [update] updates a input * state with a new input.*)

    Definition update (st : input * state) (i : input) : input * state :=
        (i, snd st).

    (** The function [freeze] makes a input * state predicate independent
        of the value of the input by quantifying them existentially *)

    Definition freeze (p : input * state -> Prop) : input * state -> Prop :=
        fun (st : input * state
) => let (i,o) := st in exists i, p (i,o).

    Lemma freeze_prop : 
        forall (p : input * state
 -> Prop) (st : input * state
 ), p st -> freeze p st.
    Proof.
        intros.
        destruct st as [i o].
        exists i.
        exact H.
    Qed.
        
    Lemma freeze_prop2 : 
        forall p st i, freeze p st -> freeze p (update st i).
    Proof.
        intros.
        unfold freeze in *.
        destruct st as [i0 o0].
        simpl.
        auto.
    Qed.
        
    (** We define the product automaton of i_aut and o_aut *)

    Definition io_aut := product i_aut o_aut.

    Notation io_step_type := 
        ((input -> Prop) * (input * state
 -> Prop) * (node1 * node2)).
    Notation io_path_type := (list io_step_type ).

    (** Obviously, in the product automaton, each node as a least a successor *)

    Lemma io_aut_successors : 
        forall n, reachable io_aut  n -> 
            exists g m, transition io_aut n g m.
    Proof.
        intros.
        assert (reachable_from i_aut (init i_aut) (fst n)).
        {
            destruct n.
            simpl.
            apply reachable_left_proj in H.
            apply H.
        }
        assert (reachable_from o_aut (init o_aut) (snd n)).
        {
            destruct n.
            apply reachable_right_proj in H.
            apply H.
        }
        apply i_aut_successors in H0.
        apply o_aut_successors in H1.
        destruct H0 as [f [n1 Ha]].
        destruct H1 as [g [m1 Hb]].
        exists (f,g), (n1,m1).
        split; assumption.
    Qed. 
        
    (* il doit y avoir un successeur par f *)
    (* le noeud doit être accessible *)

    (** Now we define the constraints that should be satisfied 
        by nodes of the product automaton which are assumed to 
        be checked by an external tool *)

    Definition next_gen (n : node1 * node2) (f : input -> Prop) 
        (n' : node1) : input * state -> Prop := 
            fun x => exists g m, transition io_aut n (f,g) (n',m) /\ g x.

    Definition prev_gen (n : node1 * node2) : input * state -> Prop :=
        fun x => exists f g m, transition io_aut m (f,g) n /\ g x.

    Definition validInit := 
        forall (f : input -> Prop) (n : node1) (i : input) (st:state),
            (exists g m, transition io_aut (init io_aut) (f,g) m ) ->
            P_init st -> f i -> next_gen (init io_aut) f n (i, program (i,st)).

    Definition validNode (n : node1 * node2) :=
        forall (f : input -> Prop) (n0 : node1) (i :input) (st : state),
            (exists g m, transition io_aut n (f,g) m ) ->
            freeze (prev_gen n) (i,st) -> f i ->
            next_gen n f n0 (i, program (i,st)).
        
    Definition validAutomata := 
        validInit /\ (forall n, reachable io_aut n -> validNode n).

End Verif.

Module Correctness (Import D : Verif_Domain).

    Module Import M := Verif D.    

    Notation trace := (list (input * state)).
    Notation inputs := (List.map (@fst input state)).

    Inductive run : D.state -> trace -> Prop :=
        | run_nil : forall st, run st nil
        | run_start : forall i st, 
            run st (cons (i, D.program (i, st)) nil)
        | run_cons : forall st i0 st0 i1 st1 l,
            run st ((i0,st0)::l) ->
            D.program (i1,st0) = st1 ->
            run st ((i1,st1)::(i0,st0)::l).

    Proposition correctness_aux : 
        forall (st : state) (tr : trace), 
            validAutomata -> 
            D.P_init st -> run st tr -> 
            forall is, language_w sat i_aut is (inputs tr) ->
                exists p, left_proj p = is /\
                    language_w sat_product io_aut p tr.
    Proof.
        intros o_start tr [cond_init cond_node] o_start_valid run.
        induction run as 
            [ o_start | i0 o_start |  
                o_start i_k o_k i_Sk o_Sk tr run tr_lang step ]; 
        intros is input_lang; simpl in *.
        -   replace is with (nil : list ((input -> Prop) * node1)) by
                now rewrite (language_w_nil _ _ _ _ _ _ input_lang).
            exists nil.
            split; [reflexivity | apply language_empty].
        -   destruct input_lang as [H_path H_valid].
            destruct is as [ | [f n1] is]; [ inversion H_valid |].
            destruct is as [ | ];
                inversion H_valid as [ | ? ? ? ? H_valid' ]; 
                inversion H_valid'; subst.           
            assert (transition i_aut (init i_aut) f n1 /\ sat f i0)
                as [h_transition input_hd_is_valid] by
                    now (inversion H_path; subst).
            assert (exists g m, 
                transition io_aut (init i_aut, init o_aut) (f,g) (n1, m) /\ 
                    g (i0, program (i0, o_start))) as [g [m [Hu Hw]]].
            {
                assert (next_gen (init D.i_aut, init D.o_aut) f n1 (i0, D.program (i0,o_start))) as H_next_gen.
                {
                    assert (exists (g : input * state
             -> Prop) (m : node1*node2), transition io_aut (init io_aut) (f, g) m) as Hy.
                    {
                        assert (reachable_from o_aut (init o_aut) (init o_aut)) as H_reach by (left; reflexivity).
                        destruct (o_aut_successors (init o_aut) H_reach) as [g [m H_trans]].
                        exists g, (n1, m); easy.
                    }
                    exact (cond_init _ _ _ _ Hy o_start_valid input_hd_is_valid).
                }
                destruct H_next_gen as [g [m' [H_transition_io H_g]]].
                exists g, m'; easy.
            }
            exists (cons ((f,g), (n1,m)) nil).
            split; [reflexivity|].
            split.
            +   exact (path_transition _ _ _ _ _ _ Hu). 
            +   assert (sat_product (f, g) (i0, program (i0, o_start))) as H_sat
                    by (split; [exact input_hd_is_valid | exact Hw]).
                exact (valid_cons _ _ _ _ _ _ _ (valid_nil _ _ _) H_sat).
        -   subst.
            destruct is as [ | [f_Sk n_SSk] is];
                [destruct input_lang as [_ Hq2]; inversion Hq2 |].
            assert (f_Sk i_Sk) as Hp4.
            {
                destruct input_lang as [_ H_valid].
                inversion H_valid as [ | ? ? ? ? _ H_sat]; subst.
                exact H_sat.
            }
            assert (language_w sat i_aut is (i_k :: inputs tr)) as input_prev_lang
                by exact (language_prefix_closed _ _ _ _ _ _ _ _ _ input_lang).
            specialize (tr_lang o_start_valid is input_prev_lang).
            destruct tr_lang as [p_io [H_peq [p_io_path p_io_valid]]].
            destruct p_io as [ | [[f_k g_k] [n_Sk m_Sk]] p_io]; [inversion p_io_valid|].
            assert (reachable_from io_aut (init i_aut, init o_aut) (n_Sk, m_Sk)) as Hp1.
            {
                right.
                exists (f_k, g_k), p_io.
                apply p_io_path.
            }
            assert (exists g_Sk m_SSk, transition io_aut (n_Sk, m_Sk) (f_Sk, g_Sk) (n_SSk, m_SSk)) as Hp2.
            {
                assert (transition i_aut n_Sk f_Sk n_SSk) as Hx.
                {
                    inversion input_lang; subst.
                    inversion H; subst.
                    exact H7.
                }
                assert (exists g_Sk m_SSk, transition o_aut m_Sk g_Sk m_SSk) as [g_Sk [m_SSk H_u]].
                {
                    apply o_aut_successors.
                    right.
                    exists g_k.
                    exists (List.map (fun p => (snd (fst p), snd (snd p))) p_io).

                    apply path_right_proj in p_io_path.
                    apply p_io_path.
                }    
                exists g_Sk, m_SSk.
                split.
                apply Hx.
                apply H_u.
            }
            
            destruct Hp2 as [g_Sk [m_SSk Hp2]].
            assert (next_gen (n_Sk, m_Sk) f_Sk n_SSk (i_Sk, program (i_Sk, o_k))).
            {
                apply cond_node.
                -   apply Hp1.
                -   exists g_Sk, (n_SSk, m_SSk).
                    apply Hp2. (* move aux here*)
                -   unfold prev_gen.        
                    inversion p_io_path; subst.
                    *   exists i_k, f_k, g_k, (init i_aut, init o_aut).
                        split.
                        exact H0.
                        inversion p_io_valid; subst.
                        apply H5.
                    *   exists i_k, f_k, g_k, m0.
                        split.
                        exact H3.
                        inversion p_io_valid; subst.
                        apply H6.
                -   apply Hp4.
            }
            destruct H as [g_z [m_z [Hz1 Hz2]]].
            exists (
                cons (f_Sk, g_z, (n_SSk,m_z))
                (cons 
                (f_k, g_k, (n_Sk, m_Sk))
                p_io)).
                split.
                *   simpl.
                    f_equal.
                    apply H_peq.
                *   split.
                    --  exact (path_transitive _ _ _ _ _ _ _ _ _ p_io_path Hz1). 
                    --  apply valid_cons.
                        ++  apply valid_cons.
                            inversion p_io_valid; subst.
                            apply H2.
                            inversion p_io_valid; subst.
                            apply H4.
                        ++  split; [exact Hp4 | exact Hz2].
    Qed.

    Theorem correctness : 
        forall (st : state) (tr : trace), 
            validAutomata -> 
            D.P_init st -> run st tr -> 
            language sat i_aut (inputs tr) ->
            language sat o_aut tr.
    Proof.
        intros o_start tr H_valid H_init H_run H_lang_input.
        destruct H_lang_input as [is Hu].
        destruct (correctness_aux _ _ H_valid H_init H_run is Hu) as [io_p [Ha Hb]].
        exists (right_proj io_p).
        destruct Hb.
        split.
        -   apply path_right_proj in H.
            apply H.
        -   rewrite <- temp0.
            replace tr with (map id tr).
            apply valid_right_proj with (sat_product := sat_product).
            intros.
            apply H1.
            apply H0.
            apply map_id.
    Qed.

End Correctness.


