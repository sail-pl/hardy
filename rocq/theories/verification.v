From Hardy Require Import automaton product.
From Stdlib Require Import List.

(* helper lemmas *)
Fact split_cons {A B} (l : list (A * B)) x y: 
    List.split ((x,y) :: l) = 

        (
            x :: fst (split l), 
            y :: snd (split l)
        )   
.
Proof.
    revert x y. induction l.
    - intros. now cbn.
    - destruct a as [x y]. intros. rewrite IHl. cbn. now destruct (split l).
Qed.


Fact split_inv {A B} (l: list (A*B)) x y x_l y_l: 
    (x_l, y_l) = split ((x,y):: l)
    <-> (
    exists x_tl y_tl,
    (x_tl, y_tl) = split l /\
    x_l = x :: x_tl
    /\
    y_l = y :: y_tl 
    )
.
Proof.
    revert x y x_l y_l. destruct l as [|[x' y'] l']; intros; split.
    - intros H. inversion_clear H. now exists nil,nil.
    - intros (x_tl & y_tl & Hsplit & Hxeq & Hyeq). cbn. inversion Hsplit. now subst.
    - intros H. cbn in H |- *. destruct (split l') eqn:X. inversion_clear H; subst. 
        now exists (x' :: l), (y' :: l0).
    - intros (x_tl & y_tl & Hsplit & Hx & Hy). subst.  cbn in *. destruct (split l') eqn:X. now inversion Hsplit.
Qed.


Definition trace {A} : Type := list A.
Definition trace_prefixes {A : Type} : Type := @trace (@trace A * A). 



Parameter input output state : Type.


Abbreviation input_trace := (@trace input).
Abbreviation output_trace := (@trace output). 
Abbreviation state_trace := (@trace state). 



(* 
    an element ((i,m)(o,m')) of a trace represent the memory m' and output o produced by the program after receiving input i and memory m

    invariant : for a valid run, m must be the same as previous m'
*)
Definition pgrm_trace : Type := @trace ((input*state)*(output*state)). 

Definition pgrm_trace_split : pgrm_trace -> (input_trace * state_trace) * (output_trace * state_trace)  := fun tr =>
    (List.split (fst (List.split tr)), List.split (snd (List.split tr))).

Definition trace_to_input_trace : pgrm_trace -> input_trace := fun tr =>  
    fst (fst (pgrm_trace_split tr)).

Definition pgrm_trace_combine : (input_trace * state_trace) * (output_trace * state_trace) -> pgrm_trace := fun '((i,m),(o,m')) =>
    List.combine (List.combine i m) (List.combine o m').

Fact pgrm_trace_split_cons tr i o m m' : 
    pgrm_trace_split (((i,m),(o,m')):: tr) = 
    (
        (
            i ::fst (fst (pgrm_trace_split tr)), 
            m :: snd (fst (pgrm_trace_split tr))
        ),
        (
            o :: fst (snd (pgrm_trace_split tr)),
            m' :: snd (snd (pgrm_trace_split tr))
        )
    )
.
Proof.
    cbn. unfold pgrm_trace_split. rewrite <- split_cons. rewrite <- split_cons. f_equal; now rewrite split_cons.
Qed.

Fact pgrm_trace_split_inv tr i m o m' i_t m_t o_t m_t' : 
    ((i_t, m_t), (o_t, m_t')) = pgrm_trace_split (((i,m),(o,m')):: tr)
    <-> (
    exists i_tl m_tl o_tl m_tl',
    ((i_tl,m_tl), (o_tl,m_tl')) = pgrm_trace_split tr /\
    i_t = i :: i_tl
    /\
    m_t = m :: m_tl  
    /\
    o_t = o :: o_tl
    /\
    m_t' = m' :: m_tl'
    )
.
Proof.
    split.
    - intros H. inversion H. unfold pgrm_trace_split. destruct (split tr) eqn:tr_eq. 
        apply split_inv in H1 as (x_tl & y_tl & Hsplit & Hx & Hy) , H2 as (x_tl' & y_tl' & Hsplit' & Hx' & Hy'). subst.
        exists x_tl, y_tl, x_tl', y_tl'. cbn. repeat split; auto. now rewrite <- Hsplit, <- Hsplit'.
    - intros (i_tl & m_tl & o_tl & m_tl' & Hsplit & Hit & Hmt & Hot & Hmt'). subst.
        unfold pgrm_trace_split in *. cbn. destruct (split tr). inversion Hsplit. cbn. now rewrite <- H0, <- H1. 
Qed.


Lemma split_combine_trace t : t = pgrm_trace_combine (pgrm_trace_split t).
Proof.
    induction t.
    - easy.
    - unfold pgrm_trace_combine, pgrm_trace_split in *; cbn.
        destruct (split t) as [im om'] eqn:Heq_t; cbn.
        pose proof length_fst_split im as Hi; pose proof length_snd_split im as Hm. 
        pose proof length_fst_split om' as Ho; pose proof length_snd_split om' as Hm'. 
        destruct (split im) as [i m] eqn:Heq_im; cbn in *.
        destruct (split om') as [o m'] eqn:Heq_om'; cbn in *.
        destruct a as ((a_i,a_m),(a_o,a_m')) eqn:Heq2. cbn.  
        destruct (split im) eqn:Hbla; destruct (split om') eqn:Hbla'; cbn; subst. now inversion Heq_om'. 
Qed.

Lemma combine_split_trace (i_t: input_trace) (m_t m_t': state_trace) (o_t : output_trace) :
    List.length i_t = List.length m_t /\
    List.length m_t = List.length m_t'/\
    List.length o_t = List.length m_t 
    ->
    ((i_t,m_t),(o_t, m_t')) = pgrm_trace_split (pgrm_trace_combine ((i_t,m_t),(o_t,m_t'))).
Proof.
    revert i_t m_t o_t m_t'.
    intros i_t.
    remember (length i_t) as n . revert Heqn. revert i_t. induction n.
    - intros * Hi_t * (Hm_t & Ho_t & Hm_t'). symmetry in Hi_t, Hm_t, Ho_t.
        rewrite Hm_t in Ho_t, Hm_t'. apply length_zero_iff_nil in Hi_t, Hm_t, Hm_t', Ho_t. now subst.
    - intros * Hi_t * (Hm_t & Ho_t & Hm_t'). 
        destruct i_t as [| i i_t]; [easy|]; 
        destruct m_t as [| m m_t]; [easy|]; 
        destruct o_t as [| o o_t]; [easy|].
        destruct m_t' as [| m' m_t']; [easy|].
        inversion Hi_t as [Hi_t2];
        inversion Ho_t as [Ho_t2];
        inversion Hm_t as [Hm_t2];
        inversion Hm_t' as [Hm_t'2].
        specialize (IHn _ Hi_t2 _ _ _ (conj Hm_t2 (conj Ho_t2 Hm_t'2))).
        cbn in *. revert IHn. set (combine (combine i_t m_t) (combine o_t m_t')) as tl. intros IHn.
        unfold pgrm_trace_split in *.
        cbn in *. 
        destruct (split tl). cbn in *.
        subst. now inversion IHn.
Qed.
    



Definition f_hist {X : Type} x acc : @trace_prefixes X := match acc with 
    | nil => (nil,x)::nil 
    | h::t => (snd h::fst h,x)::h::t 
end.

Fact f_hist_inv : forall A x tr x' tr' tr_tl, 
    (tr', x') :: tr_tl = @f_hist A x tr ->
    x' = x
.
Proof.
    intros. destruct tr; now inversion H.
Qed.


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

Definition f : Type := input * state -> output * state.

Record Program : Type := {
    setup: state;
    loop: f;
}.

(* run P l is the trace produced by executing the program P *)
Inductive run (P : Program) : pgrm_trace -> Prop :=
    | run_start i o m' : 
        loop P (i,setup P) = (o,m') ->
        run P (((i,setup P),(o,m'))::nil)
    
    | run_next tr prev_i prev_o prev_m i o m m' : 
        run P (((prev_i, prev_m), (prev_o, m))::tr) ->
        loop P (i,m) = (o,m') ->
        run P (((i,m),(o,m'))::((prev_i, prev_m),(prev_o, m))::tr)
.

Fact run_m_m' (P: Program ) tr prev_i prev_o prev_m i m o m' : 
    run P (((i,m),(o,m'))::((prev_i,m),(prev_o,prev_m))::tr) -> 
    prev_m = m 
.
Proof.
    intros H. now inversion H.
Qed.

(* property made up of the history of previous inputs, states and outputs and current input and state *)
Definition local_precond : Type :=  pgrm_trace -> (input*state) -> Prop.
Definition local_postcond : Type :=  pgrm_trace -> (input*state) -> (output*state) -> Prop.



(* hardy's output: hoare triples *)
Record HoareTriple : Type := mkTriple {
    local_pre : local_precond;
    body : f;
    local_post : local_postcond;
}.

(* what the deductive verifier proves for each triple *)
Definition valid_triple (T:HoareTriple) tr i m o m' : Prop := 
    local_pre T tr (i,m) -> 
    body T (i,m) = (o,m') ->
    local_post T tr (i,m) (o,m')  
.


(* 'assumes' automata transition label: predicate on previous inputs and current input *)
Definition a_aut_label : Type := @trace input -> input -> Prop.

Definition sat_a (p: a_aut_label) '((t,i): @trace input * input) : Prop := p t i.

(* 'guarantees' automata transition label: predicate on trace history, current input and memory, and next output and memory  *)
Definition g_aut_label : Type :=  pgrm_trace -> (input*state) -> (output*state) -> Prop.

Definition sat_g (p: g_aut_label) '((t,(im,om')): @pgrm_trace * ((input * state) * (output * state))) : Prop :=
    p t im om'.


Parameter a_aut_node : Type.

Parameter g_aut_node : Type.


(* hardy's input: temporal contracts defined as büchi automata *)
Record Contract : Type := {
    contract_setup : state -> Prop;
    contract_assumes : automaton a_aut_node a_aut_label;
    contract_guarantees : automaton g_aut_node g_aut_label;
}.


(* given a stream of inputs accepted by a_aut, the program always produces a stream of outputs accepted by g_aut *)
Definition valid_contract (C: Contract) (P: Program): Prop := 
    (contract_setup C) (setup P) ->
    forall tr, run P tr ->
    forall i_t m_t o_t,  (i_t,m_t,o_t) = pgrm_trace_split tr ->
    language sat_a (contract_assumes C) (build_trace_history i_t) -> 
    language sat_g (contract_guarantees C) (build_trace_history tr)
.


Definition aut_complete {N L} (a: automaton N L): Prop := 
    forall n, reachable a n -> exists p m, transition a n p m.

Lemma prod_complete {N1 N2 L1 L2} (a: automaton N1 L1) (b : automaton N2 L2) : 
    aut_complete a -> 
    aut_complete b ->
    aut_complete (product a b).
Proof.
    intros * Ha Hb n H.
    assert (reachable a (fst n)).
    {
        destruct n.
        simpl.
        apply reachable_left_proj in H.
        apply H.
    }
    assert (reachable b (snd n)).
    {
        destruct n.
        apply reachable_right_proj in H.  
        apply H.
    }
    apply Ha in H0 as [f [n1 Hat]].
    apply Hb in H1 as [g [m1 Hbt]].
    exists (f,g), (n1,m1).
    split; assumption.
Qed.


Definition aut_deterministic {N L A} (a: automaton N L) (belongs : L -> A -> Prop) : Prop := 
    forall w p p', 
    language_wit belongs a p w ->
    language_wit belongs a p' w ->
    p = p'
.


Lemma prod_deterministic {N1 N2 L1 L2 A B} (a: automaton N1 L1) (b : automaton N2 L2) (a_belongs : L1 -> A -> Prop) (b_belongs : L2 -> B -> Prop): 
    aut_deterministic a a_belongs ->
    aut_deterministic b b_belongs ->
    aut_deterministic (product a b) (fun '(x,y) '(a,b) => a_belongs x a /\ b_belongs y b).
Proof.
Admitted.



Section Reduction.
    Variable P : Program.
    Variable C : Contract.

    Definition a_aut := contract_assumes C.
    Definition g_aut := contract_guarantees C.



    (* Lemma aut_deterministic_local_choice {N L A} (a: automaton N L) (belongs : L -> A -> Prop)  : 
        aut_deterministic a belongs ->
        forall w n m m' p p',

        exists p, path atm (init atm) p /\ 
                valid (List.map fst p) w.
                
                
        valid belongs p w ->
        transition a n p m ->
        transition a n p' m' -> 
        p = p'
    . *)


    

    Parameter a_aut_complete : aut_complete a_aut.
    Parameter g_aut_complete : aut_complete g_aut.

    Parameter a_aut_deterministic : aut_deterministic a_aut sat_a.
    Parameter g_aut_deterministic  : aut_deterministic g_aut sat_g.
    
    Abbreviation ag_aut_node := (a_aut_node * g_aut_node)%type.
    Abbreviation ag_aut_label  := (a_aut_label * g_aut_label)%type.

    Definition ag_aut : automaton ag_aut_node ag_aut_label := product (contract_assumes C) (contract_guarantees C).

    Fact ag_aut_complete : aut_complete ag_aut.
    Proof.
        apply prod_complete; [exact a_aut_complete| exact g_aut_complete].
    Qed.


    Definition sat_ag (l: ag_aut_label) '((t,((i,m),(o,m'))): @pgrm_trace * ((input * state) * (output * state))): Prop :=
        sat_a (fst l) (trace_to_input_trace t,i) /\ 
        sat_g (snd l) (t,((i,m),(o,m')))
    .




    (* converts a postcondition for instant n into a precondition for instant n+1  *)
    Definition postcond_to_precond (post: local_postcond) : local_precond := fun t => match t with
    | nil => fun _ => True (* no history *)
    | prev_inst::h =>  
        fun _ => (* we discard current instant as the postcondition cannot mention it *)
        post h (fst (fst prev_inst), snd (fst prev_inst)) (fst (snd prev_inst), snd (snd prev_inst))
    end.

    (* disjunction of all predecesssors postcondition as precondition *)
    Inductive join_preds tr i m : ag_aut_node -> Prop :=
    | join_preds_setup :
        tr = nil /\ contract_setup C m ->
        join_preds tr i m (init ag_aut) 

    | join_preds_cons prev_n precond curr_n : 
        predecessor _ _ ag_aut prev_n precond curr_n -> 
        postcond_to_precond (snd precond) tr (i,m) ->
        join_preds tr i m curr_n
    .  

    (* join_succs n pre tr i m o m' is the disjunction of all successors (pre',post) with a precondition equivalent to pre such post tr i m o m' *)
    Inductive join_succs curr_node pre tr i m o m' : Prop := 
    | join_succs_ pre' post' next_n  :
        successor _ _ ag_aut next_n (pre',post') curr_node ->
        pre' (trace_to_input_trace tr) i <-> pre (trace_to_input_trace tr) i ->
        post' tr (i,m) (o,m') ->
        join_succs curr_node pre tr i m o m'
    .  


    (* triple_gen t n pre tr i m o m' is the triple t generated for node n for the given precondition *)
    Inductive triple_gen (t: HoareTriple) curr_node pre tr i m o m' : Prop := 
    | triple_gen_cons :
        
        
        (* the triple precondition must be equivalent to the conjunction of the disjunction of previous postconditions and current precondition *)
        (   local_pre t tr (i,m) 
            <-> 
            (join_preds tr i m curr_node /\ pre (trace_to_input_trace tr) i)
        ) 
        ->
        
        (* the triple postcondition is the disjunction of all postconditions of successors nodes with equivalent precondition  *)
        (
            local_post t tr (i,m) (o,m') <-> join_succs curr_node pre tr i m o m'
        ) ->
        body t = loop P ->
        triple_gen t curr_node pre tr i m o m'
    .


    (* each outgoing transition is associated with one more multiple triples *)
    Definition valid_generated_triples  : Prop := 
        forall n , 
        reachable ag_aut n ->
        forall pre post next_n,  successor _ _ ag_aut next_n (pre,post) n  ->
        forall tr i m o m',
        exists t, triple_gen t n pre tr i m o m' /\ valid_triple t tr i m o m'
    .

End Reduction.


Abbreviation ag_aut_node := (a_aut_node * g_aut_node)%type.
Abbreviation ag_aut_label  := (a_aut_label * g_aut_label)%type.

Definition valid_contract_wit (C: Contract) (P: Program): Prop := 
    (contract_setup C) (setup P) ->
    forall i m o m' tr, 
    run P (((i,m),(o,m'))::tr) ->
    forall i_tr m_tr o_tr m'_tr,
    ((i_tr,m_tr),(o_tr,m'_tr)) = pgrm_trace_split tr ->
    
    forall a_p a_curr_trans a_next_node, 
        language_wit sat_a (contract_assumes C) ((a_curr_trans,a_next_node)::a_p) (build_trace_history (i::i_tr)) -> 

    exists ag_p, left_proj ag_p = a_p /\        
    exists ag_curr_trans ag_next_node, 
        language_wit sat_ag (ag_aut C) ((ag_curr_trans, ag_next_node)::ag_p) (build_trace_history (((i,m),(o,m'))::tr)) 
        (* /\ (fst ag_curr_trans i_tr i <-> a_curr_trans i_tr i) *)
.

Lemma valid_contract_wit_valid C P : valid_contract_wit C P -> valid_contract C P.
Proof.
    intros  Hvalid_wit Hvalid_setup tr Hrun i_tr m_tr [o_tr m'_tr] Hsplit Ha_lang.
    destruct Ha_lang as (a_path & Ha_path & Ha_path_valid). destruct a_path as [|[a_curr_label a_next_node] a_path].
    -   (* empty path -> empty trace -> trivially sat *)
        cbn in Ha_path_valid. inversion Ha_path_valid. symmetry in H; apply -> build_trace_history_iff_h_nil in H. subst. destruct tr eqn:X;[easy|].
        destruct p as [[i m] [o m']].
        pose proof  pgrm_trace_split_cons p0 i o m m'. now rewrite H in Hsplit. 

    - destruct tr as [|[[i m] [o m']] tr];[easy|]. 
        pose proof Hsplit as Hsplit'.
        apply pgrm_trace_split_inv in Hsplit as (i_tl & m_tl & o_tl & m'_tl & Hsplit & Heq1 & Heq2 & Heq3 & Heq4); subst.
    
        specialize (Hvalid_wit Hvalid_setup _ _ _ _ _ Hrun _ _ _ _ Hsplit _ _ _ (conj Ha_path Ha_path_valid))
         as (ag_path & Hleft_proj & [a_curr_label' g_curr_label] & [a_next_node' g_next_node] & Hag_path_valid ). 
         rewrite build_trace_history_cons in *.
        inversion_clear Hag_path_valid as [Hag_path Hag_path_valid'];  cbn in *.
        exists ((g_curr_label,g_next_node)::right_proj ag_path); split. 
    
        + now apply path_right_proj in Hag_path.
        + apply valid_right_proj  with  (sat:= sat_g) (transf:=id) in Hag_path_valid'.
            * cbn in *. inversion Hag_path_valid'; subst; cbn in *. rewrite map_id in H2. constructor; [|assumption].
                replace (map fst (right_proj ag_path)) with (map snd (map fst ag_path));[assumption|].
                clear. induction ag_path; [reflexivity|simpl; f_equal; apply IHag_path].

            * intros * Hsat_ag. red in Hsat_ag. now destruct b as [tr' [[i0 m0 ] [o0 m'0]]].  
Qed.

Theorem correctness_aux P C: 
    valid_generated_triples P C -> 
    valid_contract_wit C P. 
Proof.
    intros Htriples Hvalid_setup i m o m' tr. revert i m o m'. induction tr.  

    - intros i m o m' Hrun. (* first instant  *) 
        inversion Hrun; subst.
        intros i_tr m_tr o_tr m'_tr Htr_split a_path a_curr_label a_next_node Ha_lang.
        inversion Htr_split; subst.
        rewrite build_trace_history_cons in Ha_lang |- *.


        (* get current a_aut transition *)
        inversion Ha_lang as (Ha_path & Ha_path_valid). 
        inversion Ha_path_valid as [|? ?  ? ? Ha_path_valid_prev Ha_curr_valid]; subst.
        destruct a_path; [|easy].
        
        (* moreover, we have a transition in the assumes automaton from the initial node to a_n *)
        inversion Ha_path as [x|? ? Ha_trans x|x]; subst.

        (* we now show we also have a transition in ag_aut from the initial node to (a_n,g_n) such that
        its right component g_postcond satisfy the program first postcondition  *)
         assert (exists g_curr_label g_next_node, 
            transition (ag_aut C) (init (a_aut C), init (g_aut C)) (a_curr_label,g_curr_label) (a_next_node, g_next_node) /\ 
           (join_succs C (init (a_aut C), init (g_aut C)) a_curr_label nil i (setup P) o m')
        ) as (g_curr_label & g_next_node & [ag_aut_trans Hsuccs]).
        {

            (* we have a transition in ag_aut from the initial node to (a_n,g_n) *)
            assert (exists (g_curr_label : g_aut_label) g_next_node,
                            transition (ag_aut C) (init (ag_aut C)) (a_curr_label, g_curr_label) (a_next_node,g_next_node)) 
            as (g_curr_label & g_next_node & Hag_trans).
            {
                    assert (reachable (g_aut C) (init (g_aut C))) as H_reach by (left; reflexivity).
                    destruct (g_aut_complete C (init (g_aut C)) H_reach) as [g [g_n H_trans]].
                    exists g, g_n; easy.
            }

            exists g_curr_label, g_next_node; split; cbn; [assumption|].
                               
            assert (Hinitreach : reachable (ag_aut C) (init (a_aut C), init (g_aut C))) by now constructor.
            specialize (Htriples _ Hinitreach _ _ _ Hag_trans nil i (setup P) o m') as (t & Htriples_gen & Htriples_valid).
            inversion_clear Htriples_gen as [Hpre Hpost Ht_body]. apply Hpost.
           
            (* this gives us the postcondition *)
            apply Htriples_valid; [|now rewrite Ht_body]. 
            rewrite Hpre; cbn; split; [|assumption]. now constructor.
        }

        exists nil. split; [now constructor|]. inversion Hsuccs as [a_curr_label' g_curr_label' [a_next_node' g_next_node'] ag_succ Ha_label_equiv Hg].
        
        (* ag_succ is the same path as ag_aut_trans *)
        assert (Heq: (a_curr_label',g_curr_label') = (a_curr_label, g_curr_label) /\ (a_next_node', g_next_node') = (a_next_node, g_next_node)) by admit.
        destruct Heq as [H1 H2]; inversion H1; inversion H2; subst.

        exists (a_curr_label, g_curr_label), (a_next_node,g_next_node). split; [now constructor|]; constructor; [now constructor|now split].

    - intros i m o m' Hrun.  (* nth instant *)
        inversion Hrun as [|? ? ? ? ? ? ? ? Hrun' Hloop]; subst.
        intros i_tr m_tr o_tr m'_tr Htr_split a_path a_curr_label a_next_node Ha_lang.
        apply pgrm_trace_split_inv in Htr_split
            as  (i_tr' & m_tr' & o_tr' & m'_tr' & Htr_split & Hit & Hmt & Hotr & Hmt').
        inversion Hit; inversion Hmt; inversion Hotr; inversion Hmt'; subst; clear H H0 H1 H2;
        rename i_tr' into i_tr, m_tr' into m_tr, o_tr' into o_tr, m'_tr' into m'_tr.
        
        do 2 rewrite build_trace_history_cons in  *.
        
        inversion Ha_lang as [Ha_path Ha_valid]; inversion Ha_valid as [|? ? ? ? Ha_prev_valid Ha_curr X Y ]; subst.
        
        pose proof language_prefix_closed _ _ _ _ _ _ _ _ _ Ha_lang as Ha_lang_prev;
        inversion Ha_lang_prev as [Ha_path_prev _].

        destruct a_path as [|[a_prev_label a_curr_node] a_path];[easy|]. 
        
        (* our induction hypothesis gives us a path in the product automaton 
            that contains the path from the assumption automaton, but with one less transition
            such that the trace up to the previous instant is valid
        *)
        specialize (IHtr _ _ _ _ Hrun' _ _ _ _ Htr_split); rewrite build_trace_history_cons in IHtr.
        specialize (IHtr _ _ _ Ha_lang_prev) as (ag_path & Hag_path_left & (a_prev_label', g_prev_label) & (a_curr_node', g_curr_node) & Hag_lang_prev).
        rewrite build_trace_history_cons in *.


        inversion Hag_lang_prev as [Hag_path_prev Hag_valid_prev]; cbn in *.
        pose proof valid_prefix_closed _ _ _ _ _ _ _ Hag_valid_prev as Hag_valid_prev_all.


    (* because automata are deterministic, we have prev_label' = a_prev_label and a_curr_node' = a_curr_node *)
        assert (a_prev_label' = a_prev_label /\ a_curr_node' = a_curr_node) as [H1 H2]. {
            pose proof path_left_proj _ _ _ _ _ _ _ _ Hag_path_prev as H; cbn in H.
            inversion Ha_path_prev.
            -  inversion H;[|now rewrite <- H3, <- H7 in Hag_path_left]. subst. admit.
            
            - inversion H;[now rewrite <- H3, <- H8 in Hag_path_left|].
                rewrite <- H3, <- H8 in Hag_path_left; inversion Hag_path_left; subst. 
                admit.
        } 

        subst.

        assert (Hag_curr_reach: reachable (ag_aut C) (a_curr_node, g_curr_node)) by (constructor 2; eauto).

        pose proof ag_aut_complete _ _ Hag_curr_reach as ([a_curr_label' g_curr_label] & ag_next_node & Hag_trans).
        inversion Hag_trans as [Ha_trans' Hg_trans]. 

        inversion Ha_path as [X|?|? ? ? ? ?  _ Ha_trans]; subst. cbn in Ha_trans', Hg_trans.

        assert (a_curr_label' = a_curr_label /\ a_next_node = fst ag_next_node) as [H1 H2]  by admit; subst. 
        
        specialize (Htriples _ Hag_curr_reach _ _ _ Hag_trans ((prev_i, prev_m, (prev_o, m)) :: tr) i m o m') as (t & Htriple_gen & Hvalid_triple).
        destruct Htriple_gen as [Ht_pre Ht_post Ht_body ].

        assert (Ha_curr_sat : a_curr_label (trace_to_input_trace ((prev_i, prev_m, (prev_o, m)) :: tr)) i). {
            unfold trace_to_input_trace in Ht_pre |- * ; rewrite pgrm_trace_split_cons in Ht_pre |- *; cbn in Ht_pre |- *; subst. 
            now inversion Htr_split.
        }

        assert (Hw_join :join_succs C (a_curr_node, g_curr_node) a_curr_label ((prev_i, prev_m, (prev_o, m)) :: tr) i m o m' -> g_curr_label ((prev_i, prev_m, (prev_o, m)) :: tr) (i, m) (o, m')).
        {
            intros Hj. inversion Hj.  
            (* as we are deterministic, post' must be g_curr_label *) 
            admit.            
        }

        exists (((a_prev_label, g_prev_label),(a_curr_node,g_curr_node))::ag_path); split; [reflexivity|].
        exists (a_curr_label, g_curr_label), ag_next_node. split; [now constructor|]; cbn. constructor; [assumption|]; constructor; [assumption|]; cbn.
        apply Hw_join; apply Ht_post; apply Hvalid_triple; [|now rewrite Ht_body]. apply Ht_pre; split; [|assumption].

        inversion Hag_path_prev; subst.
        + apply (join_preds_cons _ _ _ _ (init (ag_aut C)) (a_prev_label,g_prev_label) (a_curr_node,g_curr_node)).
            * apply H0.
            * cbn. inversion Hag_valid_prev; subst. now inversion H5.
        + apply (join_preds_cons _ _ _ _ m0 (a_prev_label,g_prev_label) (a_curr_node,g_curr_node)).
            * apply H3.
            * cbn. inversion Hag_valid_prev; subst. apply H6.
Admitted.


Corollary correctness P C : 
    valid_generated_triples P C -> 
    valid_contract C P. 
Proof.
    intros Hvalid; apply valid_contract_wit_valid; apply correctness_aux; assumption.
Qed.
