Require Import List.
From Hardy Require Import automaton product.

Module Type Verif_Domain.

    (** We assume two abstract types [input] and [state] denoting 
        inputs and states of the system. A program is a function
        mapping pairs of inputs and states to states.
        -   The predicate [P_init] describes the inital state of the system
        -   The bucchi automaton [i_aut] describes the input of the system.
        -   The bucchi automaton [o_aut] describes the expected state of 
            the system 
        We assume that in both automata, each node has at least one sucessor.
    *)

    Definition successor {N L : Type} (a: automaton N L) := forall n,
        reachable a n -> exists p m, transition a n p m.


    Parameter input state : Set.

    Parameter P_init : state -> Prop.


    Definition history := list (input * state).

    Parameter program : input * state -> state.
    Parameter node1 node2 : Set.

    Definition i_p_type : Type := history * input -> Prop.
    Definition o_p_type : Type := history * (input * state) -> Prop.

    Definition i_step_type : Type := i_p_type * node1.
    Definition o_step_type : Type := o_p_type * node2.

    Definition i_path_type : Type := list i_step_type.
    Definition o_path_type : Type := list o_step_type.


    Parameter i_aut : automaton node1 i_p_type.
    Parameter o_aut : automaton node2 o_p_type.

    Parameter i_aut_successor : successor i_aut.
    Parameter o_aut_successor : successor o_aut.


    Definition sat_i := fun (p : i_p_type) (x : history * (input * state)) => 
        p (fst x, fst (snd x)).

    Definition sat_o := fun (p : o_p_type) (x : history * (input * state)) => 
        p x.

    (** a letter of a valid word in the product automaton is made up of an history 
        of previous (input,state) and the current (input,state). 
        As a transition is composed of two predicates [f] and [g], [f] must hold for 
        the current input and history of (input,state) and [g] must hold for the current input, 
        state and history of (input,state)
    *)
    Definition sat_product (fg : i_p_type * o_p_type) (x : history * (input * state)) := 
        sat_i (fst fg) x /\ sat_o (snd fg) x.

End Verif_Domain.
                    
Module Verif (Import D : Verif_Domain).


    (** We define the product automaton of i_aut and o_aut *)

    Definition io_aut := product i_aut o_aut.

    Definition io_step_type : Type := i_p_type * o_p_type * (node1 * node2).
    Definition io_path_type := list io_step_type.

    (** Obviously, in the product automaton, each node as at least one successor *)

    Lemma io_aut_successor : 
        forall n, reachable io_aut n -> 
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
        apply i_aut_successor in H0 as [f [n1 Ha]].
        apply o_aut_successor in H1 as [g [m1 Hb]].
        exists (f,g), (n1,m1).
        split; assumption.
    Qed.  
        

    (** Now we define the constraints that should be satisfied 
        by nodes of the product automaton which are assumed to 
        be checked by an external tool *)


    (** Given a node [n] from [io_aut] and a node [m_i] from [i_aut], there must exist a node [m_o] from [o_aut]
        which together form the successor [(m_i,m_o)] of [n] in [io_aut].
        In addition, the transition from [n] to [m] is labeled by (f,g) 
        where g holds for a certain history, input and state [h_i_s].
    *)
    Definition next_gen (n : node1 * node2) (f : i_p_type)  : o_p_type := 
            fun h_i_s => exists g m, transition io_aut n (f,g) m /\ g h_i_s.

    (** Given a node [m] from [io_aut], there must exist a node [n] which is a precedessor of [m].
        In addition, the transition from [n] to [m] is labeled by (f,g)  where g holds an 
        for a certain history, input and state [h_st].
     *)
    Definition prev_gen (m : node1 * node2) : o_p_type :=
        fun h_i_s => exists f g n, transition io_aut n (f,g) m /\ g h_i_s.

    (** The initial node [n] is valid iff given : 
    
        - any predicate on input [f] making up the first part of the label of at least one transition exiting [n] 
        - any input [i] for which [f] holds 
        - any state [st] respecting P_init, i.e. a valid initial state

        there exists a transition from [n] labeled by ([f],[g])
        where g holds for [i] and the next state of the program (there is of course no history yet).

        That is to say, given an initial state and input, any immediately following state produced 
        by the system must be correct
    *)
    Definition validInit := 
        forall (f : i_p_type) (i : input) (st:state),
            (exists g m, transition io_aut (init io_aut) (f,g) m ) ->
            P_init st -> f (nil,i) -> next_gen (init io_aut) f (nil, (i, program (i,st))).


    (** A node [n] is valid iff given :
        - any predicate on input [f] making up the first part of the label of at least one transition exiting [n]
        - any input [i] for which [f] holds 
        - any state [st] which made a predicate hold true together with a previous unknown input [prev_i] 
            and history [h]

        there exists a transition labeled [(f,g)] from [n] to some other node. 
        In addition, g holds for the next program state after receiving [i] under state [st].

        That is to say, if we have a correct state given a correct input, we must also have new correct state
        upon receiving a new input.
    *)
    Definition validNode (n : node1 * node2) :=
        forall (f : i_p_type) (i prev_i :input) (st : state) h,
            (exists g m, transition io_aut n (f,g) m ) -> f ((prev_i,st)::h,i) ->
            prev_gen n (h, (prev_i,st)) -> 
            next_gen n f ((prev_i,st)::h, (i, program (i,st))).
        

    Definition validAutomaton := 
        validInit /\ (forall n, reachable io_aut n -> validNode n).

End Verif.

Module Correctness (Import D : Verif_Domain).

    Module Import M := Verif D.    

    Definition trace := list (input * state).
    Definition inputs := List.map (@fst input state).
    Definition states := List.map (@snd input state).


    (** A running system begins with an initial state. Then, when given an input, 
        it produces a new state which stays the same until a new input is given to
        produce a new state and so on. A trace is recorded which keeps an history of pairs of
        received input and new state produced for this input. 
        The first element of the trace is the last state of the program.
    *)
    Inductive run : D.state -> trace -> Prop :=
        | run_nil : forall st, run st nil
        | run_start : forall i st, 
            run st ((i, D.program (i, st))::nil)
        | run_cons : forall st i0 st0 i1 st1 l,
            run st ((i0,st0)::l) ->
            D.program (i1,st0) = st1 ->
            run st ((i1,st1)::(i0,st0)::l).
        

    (** To be able to reason on the history inside predicates, 
        we include all the past history at each step of the trace 
    *)
    Definition trace_history := list (trace * (input * state)).

    Definition f_hist {A : Type} x acc : list (list A * A) := match acc with 
        | nil => (nil,x)::nil 
        | h::t => (snd h::fst h,x)::h::t 
    end.

    Definition build_trace_history {A : Type} : list A -> list (list A * A) := 
        fold_right f_hist nil
    .

    Fact f_hist_not_nil : forall A x  l, @f_hist A x l <> nil.
    Proof.
            intros A x l Hcontra. now destruct l.
    Qed. 

    Fact build_trace_history_iff_h_nil :  forall A h, @build_trace_history A h = nil <-> h = nil.
    Proof.
        intros. split; intros H; [|now rewrite H].
        unfold build_trace_history in H. destruct h eqn:eqnH; [reflexivity|exfalso].
        simpl in H. now apply f_hist_not_nil in H.
    Qed.

    Fact build_trace_history_cons : forall A tr h, 
        @build_trace_history A (h::tr) = (tr,h)::build_trace_history tr.
    Proof.
        induction tr; intro h; simpl in *.
        - reflexivity.
        - now rewrite IHtr at 1 2.
    Qed.

    (** if we have a valid product automaton and an initial state [st],
        for any run of the system begining with [st] and producing the trace [tr], 
        for any path [ip] in the input automaton for which each input received by the system is correct,
        there must exist a path in the product automaton whose left projection is [is] and 
        whose right projection correspond to the fact each new state produced is correct.
    *)
    Proposition correctness_aux : 
        forall (st : state) (tr : trace), 
            validAutomaton -> 
            D.P_init st -> run st tr -> 
            forall (ip:i_path_type), language_wit sat_i i_aut ip (build_trace_history tr) ->
                exists (p:io_path_type), 
                left_proj p = ip /\ language_wit sat_product io_aut p (build_trace_history tr).
    Proof.
        intros o_start tr [cond_init cond_node] o_start_valid run.
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
                (** this is given by the validInit assumption *)
                assert (H_next_gen : next_gen (init i_aut, init o_aut) f (nil, (i0, program (i0,o_start)))).
                { 
                    (** g and m are found using the fact that any reachable node must have a successor,
                        so the initial output node has a successor [m] labeled by [(f,g)]
                     *)
                    assert (Hy : exists (g : o_p_type) (m : node1*node2),
                                transition io_aut (init io_aut) (f, g) m).
                    {
                        assert (reachable o_aut (init o_aut)) as H_reach by (left; reflexivity).
                        destruct (o_aut_successor (init o_aut) H_reach) as [g [m H_trans]].
                        exists g, (n1, m); easy.
                    }
                    exact (cond_init _ _ _ Hy o_start_valid input_hd_is_valid).
                }
                destruct H_next_gen as [g [[n1' n2] [H_transition_io H_g]]].
                exists g, n2.
                split ; [|assumption].
                inversion_clear H_transition_io as [_ h_transition_o].
                exact (conj h_transition h_transition_o).
            }

            exists (((f,g), (n1,m))::nil).
            split; [reflexivity|].
            split.
            +   exact (path_transition _ _ _ _ _ _ Hu). 
            +   assert (sat_product (f, g) (nil, (i0, program (i0, o_start)))) as H_sat
                    by (exact (conj input_hd_is_valid Hw)).
                exact (valid_cons _ _ _ _ _ _ _ (valid_nil _ _ _) H_sat).

        -  subst.
        
            rewrite build_trace_history_cons in tr_lang.
            rewrite build_trace_history_cons,build_trace_history_cons in input_lang.
            simpl in input_lang, tr_lang.

            (** because the system received at least 2 valid inputs, the path taken in [i_aut] is at least of size 2.
                More precisely, the label [f_Sk] of the last transition of the path must satisfy the last input [i_Sk]
                and the label [f_k] of the previous transition must satisfy the previous input [i_k]. 
            *)
            destruct ipath as [ | [f_Sk n_SSk] ipath];
                [destruct input_lang as [_ Hq2]; inversion Hq2 ;
                symmetry in H; apply map_eq_nil in H; now apply f_hist_not_nil in H
                |].
            assert (Hp4 : f_Sk ((i_k, o_k) :: tr,i_Sk)).
            {
                destruct input_lang as [_ H_valid]. 
                inversion H_valid as [| ? ? ? ? _ H_sat]; subst.
                exact H_sat.
            }


            assert (input_prev_lang : language_wit sat_i i_aut ipath ((tr, (i_k,o_k)) ::(build_trace_history tr)))
                by exact (language_prefix_closed _ _ _ _ _ _ _ _ _ input_lang).

            (**
                we get the path [p_io] in the product automaton which satisfy at the end the previous input [i_k].
                It cannot be empty as the word has at least 1 letter.
            *)
            specialize (tr_lang o_start_valid ipath input_prev_lang).
            destruct tr_lang as [p_io [H_peq [p_io_path p_io_valid]]].
            destruct p_io as [ | [[f_k g_k] [n_Sk m_Sk]] p_io]; [simpl in *; destruct (build_trace_history tr) ; inversion p_io_valid|].
            inversion p_io_valid as [|prev_letter prev_word  ? ? Hv Hs]. subst.
            
            (* we now get the right hypotheses to apply cond_node on (n_Sk, m_Sk) and obtain the io path *)

            (* (n_Sk, m_Sk) is reachable *)
            assert (Hp1 : reachable io_aut (n_Sk, m_Sk)).
            {
                right.
                exists (f_k, g_k), p_io.
                apply p_io_path.
            }

            (* (n_Sk, m_Sk) has a successor (n_SSk, m_SSk)  *)
            assert (Hp2 : exists g_Sk m_SSk, transition io_aut (n_Sk, m_Sk) (f_Sk, g_Sk) (n_SSk, m_SSk)).
            {
                assert (transition i_aut n_Sk f_Sk n_SSk) as Hx.
                {
                    inversion input_lang; subst.
                    inversion H; subst.
                    exact H7.
                }
                assert (exists g_Sk m_SSk, transition o_aut m_Sk g_Sk m_SSk) as [g_Sk [m_SSk H_u]].
                {
                    apply o_aut_successor.
                    right.
                    exists g_k.
                    exists (List.map (fun p => (snd (fst p), snd (snd p))) p_io).

                    apply path_right_proj in p_io_path.
                    apply p_io_path.
                }    
                exists g_Sk, m_SSk. exact (conj Hx H_u).
            }
            destruct Hp2 as [g_Sk [m_SSk Hp2]]. 

            assert (Hp3 : exists (g : o_p_type) (m : node1 * node2),
                transition io_aut (n_Sk, m_Sk) (f_Sk, g) m).
            {
                exists g_Sk, (n_SSk, m_SSk). apply Hp2.
            }

            assert (H : next_gen (n_Sk, m_Sk) f_Sk ((i_k, o_k) :: tr,(i_Sk, program (i_Sk, o_k)))).
            { 
                unfold validNode in cond_node.
                apply (cond_node (n_Sk, m_Sk) Hp1 f_Sk i_Sk i_k o_k tr Hp3 Hp4). 
                inversion p_io_path as [ a  | ? ? Hc | nd ? ? ? ? ? ? Hc ]; subst.
                    +   exists f_k, g_k, (init i_aut, init o_aut); firstorder.
                    +   exists f_k, g_k, nd; firstorder.
            }


            destruct H as [g_z [[m_z1 m_z2] [Hz1 Hz2]]].
            exists (
                (f_Sk, g_z, (n_SSk, m_z2))::(f_k, g_k, (n_Sk, m_Sk))::p_io
            ).
            split.
            * simpl. f_equal.
            * split.
                --  constructor. 
                    + apply p_io_path.
                    + exact (conj (proj1 Hp2) (proj2 Hz1)). 
                -- rewrite build_trace_history_cons. rewrite build_trace_history_cons. simpl.  
                    apply valid_cons.
                    ++ now apply valid_cons.
                    ++ now split.
    Qed.

    Theorem correctness : 
        forall (st : state) (tr : trace), 
            validAutomaton -> 
            D.P_init st -> run st tr -> 
            language sat_i i_aut (build_trace_history tr) ->
            language sat_o o_aut (build_trace_history tr).
    Proof.
        intros o_start tr H_valid H_init H_run H_lang_input.
        destruct H_lang_input as [is Hu].
        destruct (correctness_aux _ _ H_valid H_init H_run is Hu) as [io_p [Ha Hb]].
        exists (right_proj io_p).
        destruct Hb.
        split.
        -   apply path_right_proj in H.
            apply H.
        -   eapply valid_right_proj with (sat:=sat_o) (transf:=id) in H0.
            + replace (map fst (right_proj io_p)) with (map snd (map fst io_p)).
                ++ now rewrite map_id in H0.
                ++ clear. induction io_p ; [reflexivity|simpl; f_equal; apply IHio_p]. 
            + intros. apply H1.
    Qed.

End Correctness.


