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
        We assume that in both automata, each node has at least one sucessor.
    *)

    Definition successor {N L : Type} (a: automaton N L) := forall n,
        reachable a n -> exists p m, transition a n p m.

    Parameter input state : Set.

    Parameter program : input * state -> state.

    Parameter P_init : state -> Prop.

    Parameter node1 node2 : Set.

    Parameter i_aut : automaton node1 (input -> Prop).
    Parameter o_aut : automaton node2 (input * state -> Prop).

    Parameter i_aut_successor : successor i_aut.
    Parameter o_aut_successor : successor o_aut.

    Definition sat {A} := fun (p : A -> Prop) (x : A) => p x.

    Definition i_step_type := ((input -> Prop) * node1)%type.
    Definition o_step_type := ((input * state -> Prop) * node2)%type.
    Definition i_path_type := list i_step_type.
    Definition o_path_type := list o_step_type.

End Verif_Domain.
                    
Module Verif (Import D : Verif_Domain).

    (** The function [update] updates a input * state with a new input.*)

    Definition update (st : input * state) (i : input) : input * state :=
        (i, snd st).

        
    (** We define the product automaton of i_aut and o_aut *)

    Definition io_aut := product i_aut o_aut.

    Definition io_step_type := ((input -> Prop) * (input * state -> Prop) * (node1 * node2))%type.
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
        where g holds for a certain pair of input and state [x].
    *)
    Definition next_gen (n : node1 * node2) (f : input -> Prop)  : input * state -> Prop := 
            fun x => exists g m, transition io_aut n (f,g) m /\ g x.

    (** Given a node [m] from [io_aut], there must exist a node [n] which is a precedessor of [m].
        In addition, the transition from [n] to [m] is labeled by (f,g)  where g holds an 
        for a certain unknown input and a known state [st].
     *)
    Definition prev_gen (m : node1 * node2) : state -> Prop :=
        fun st => exists f g n, transition io_aut n (f,g) m /\ exists i, g (i,st).

    (** The initial node [n] is valid iff given : 
    
        - any predicate on input [f] making up the first part of the label of at least one transition exiting [n] 
        - any input [i] for which [f] holds 
        - any state [st] respecting P_init, i.e. a valid initial state

        there exists a transition from [n] labeled by ([f],[g])
        where g holds for [i] and the next state of the program.

        That is to say, given an initial state and input, any immediately following state produced 
        by the system is correct
    *)
    Definition validInit := 
        forall (f : input -> Prop) (i : input) (st:state),
            (exists g m, transition io_aut (init io_aut) (f,g) m ) ->
            P_init st -> f i -> next_gen (init io_aut) f (i, program (i,st)).


    (** A node [n] is valid iff given :
        - any predicate on input [f] making up the first part of the label of at least one transition exiting [n]
        - any input [i] for which [f] holds 
        - any state [st] for which   

        there exists a transition labeled (f,_) from the initial state to some other state, then

    *)
    Definition validNode (n : node1 * node2) :=
        forall (f : input -> Prop) (i :input) (st : state),
            (exists g m, transition io_aut n (f,g) m ) ->
            prev_gen n st -> f i ->
            next_gen n f (i, program (i,st)).
        

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
    *)
    Inductive run : D.state -> trace -> Prop :=
        | run_nil : forall st, run st nil
        | run_start : forall i st, 
            run st ((i, D.program (i, st))::nil)
        | run_cons : forall st i0 st0 i1 st1 l,
            run st ((i0,st0)::l) ->
            D.program (i1,st0) = st1 ->
            run st ((i1,st1)::(i0,st0)::l).


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
            forall ip, language_wit sat i_aut ip (inputs tr) ->
                exists p, left_proj p = ip /\ language_wit sat_product io_aut p tr.
    Proof.
        intros o_start tr [cond_init cond_node] o_start_valid run.
        induction run as 
            [ o_start | i0 o_start |  
                o_start i_k o_k i_Sk o_Sk tr run tr_lang step ]; 
        intros ipath input_lang; simpl in *.

        -   replace ipath with (nil : list ((input -> Prop) * node1)) by
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
                    g (i0, program (i0, o_start))) as [g [m [Hu Hw]]].
            {
                (** this is given by the validInit assumption *)
                assert (H_next_gen : next_gen (init i_aut, init o_aut) f (i0, program (i0,o_start))).
                { 
                    (** g and m are found using the fact that any reachable node must have a successor,
                        so the initial output node has a successor [m] labeled by [(f,g)]
                     *)
                    assert (Hy : exists (g : input * state -> Prop) (m : node1*node2),
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
            +   assert (sat_product (f, g) (i0, program (i0, o_start))) as H_sat
                    by (split; [exact input_hd_is_valid | exact Hw]).
                exact (valid_cons _ _ _ _ _ _ _ (valid_nil _ _ _) H_sat).

        -   subst.
            destruct ipath as [ | [f_Sk n_SSk] ipath];
                [destruct input_lang as [_ Hq2]; inversion Hq2 |].
            assert (Hp4 : f_Sk i_Sk).
            {
                destruct input_lang as [_ H_valid].
                inversion H_valid as [ | ? ? ? ? _ H_sat]; subst.
                exact H_sat.
            }
            assert (input_prev_lang : language_wit sat i_aut ipath (i_k :: inputs tr))
                by exact (language_prefix_closed _ _ _ _ _ _ _ _ _ input_lang).
            specialize (tr_lang o_start_valid ipath input_prev_lang).
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
            assert (next_gen (n_Sk, m_Sk) f_Sk (i_Sk, program (i_Sk, o_k))).
            {
                apply cond_node.
                -   apply Hp1.
                -   exists g_Sk, (n_SSk, m_SSk). apply Hp2.
                -   inversion p_io_valid as [ | ? ? ? ? Ha Hb ]; subst.
                    inversion p_io_path as [ a  | ? ? Hc | nd ? ? ? ? ? ? Hc ]; subst.
                    +   exists f_k, g_k, (init i_aut, init o_aut); firstorder.
                    +   exists f_k, g_k, nd; firstorder.
                -   exact Hp4.
            }
            destruct H as [g_z [[m_z1 m_z2] [Hz1 Hz2]]].
            exists (
                (f_Sk, g_z, (n_SSk, m_z2))::(f_k, g_k, (n_Sk, m_Sk))::p_io
            ). 
            simpl in *. 
            split.
            * f_equal. exact H_peq.
            * split.
                --  constructor. 
                    + apply p_io_path.
                    + exact (conj (proj1 Hp2) (proj2 Hz1)). 
                --  apply valid_cons.
                    ++  inversion p_io_valid as [ | ? ? ? ? Ha Hb]; subst.
                            exact (valid_cons _ _ _ _ _ _ _ Ha Hb).
                    ++  split; [exact Hp4 | exact Hz2].
    Qed.

    Theorem correctness : 
        forall (st : state) (tr : trace), 
            validAutomaton -> 
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
            replace tr with (map id tr) by apply map_id.
            apply valid_right_proj with (sat_product := sat_product).
            intros.
            apply H1.
            apply H0.
    Qed.

End Correctness.


