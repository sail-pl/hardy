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



Definition instant  : Type := ((input * state) * (output * state))%type.


(* 
    an element ((i,m)(o,m')) of a trace represent the memory m' and output o produced by the program after receiving input i and memory m

    invariant : for a valid run, m must be the same as previous m'
*)
Definition pgrm_trace : Type := @trace instant. 

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


Definition build_trace_history {A : Type} : @trace A -> trace_prefixes := 
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
Definition local_precond : Type :=  pgrm_trace -> input -> Prop.
Definition local_postcond : Type :=  pgrm_trace -> (input*state) -> (output*state) -> Prop.



(* hardy's output: hoare triples *)
Record HoareTriple : Type := mkTriple {
    local_pre : local_precond;
    body : f;
    local_post : local_postcond;
}.

(* what the deductive verifier proves for each triple *)
Definition valid_triple (T:HoareTriple) tr i m o m' : Prop := 
    local_pre T tr i -> 
    body T (i,m) = (o,m') ->
    local_post T tr (i,m) (o,m')  
.


(* 'assumes' automata transition label: predicate on previous inputs and current input *)
Definition a_aut_label : Type := @trace input -> input -> Prop.

Definition sat_a (p: a_aut_label) '((t,i): @trace input * input) : Prop := p t i.

(* 'guarantees' automata transition label: predicate on trace history, current input and memory, and next output and memory  *)
Definition g_aut_label : Type :=  pgrm_trace -> (input*state) -> (output*state) -> Prop.

Definition sat_g (p: g_aut_label) '((t,(im,om')): pgrm_trace * instant) : Prop :=
    p t im om'.


Parameter a_aut_node : Type.

Parameter g_aut_node : Type.


(* hardy's input: temporal contracts defined as büchi automata *)
Record Contract : Type := {
    contract_setup : state -> Prop;
    contract_assumes : automaton a_aut_node a_aut_label;
    contract_guarantees : automaton g_aut_node g_aut_label;
}.


(* given a stream of inputs accepted by a_aut, the program always produces a stream of inputs, outputs and memory states accepted by g_aut *)
Definition valid_contract (C: Contract) (P: Program): Prop := 
    (contract_setup C) (setup P) ->
    forall tr, run P tr ->
    forall i_t m_t o_t,  (i_t,m_t,o_t) = pgrm_trace_split tr ->
    language sat_a (contract_assumes C) (build_trace_history i_t) -> 
    language sat_g (contract_guarantees C) (build_trace_history tr)
.



Section Reduction.
    Variable C : Contract.

    Definition a_aut := contract_assumes C.
    Definition g_aut := contract_guarantees C.
    
    Abbreviation ag_aut_node := (a_aut_node * g_aut_node)%type.
    Abbreviation ag_aut_label  := (a_aut_label * g_aut_label)%type.

    Definition ag_aut : automaton ag_aut_node ag_aut_label := product (contract_assumes C) (contract_guarantees C).

    Fact ag_aut_complete : aut_complete _ _ a_aut -> aut_complete _ _ g_aut -> aut_complete _ _  ag_aut.
    Proof.
        intros Ha Hg. now apply prod_complete.
    Qed.


    Definition sat_ag (l: ag_aut_label) '((t,((i,m),(o,m'))): pgrm_trace * instant): Prop :=
        sat_a (fst l) (trace_to_input_trace t,i) /\ 
        sat_g (snd l) (t,((i,m),(o,m')))
    .


    Definition sat_ag_proj_left : pgrm_trace * instant -> input_trace * input := fun x => (trace_to_input_trace (fst x),fst (fst (snd x))).
    Definition sat_ag_proj_right : pgrm_trace * instant -> pgrm_trace * instant := id.

    Lemma sat_ag_proj_left_sat_a : forall (a : ag_aut_label) (b : pgrm_trace * instant), sat_ag a b -> 
        sat_a (fst a) (sat_ag_proj_left b).
    Proof.
        intros [? ?] [? ([? ?] & ? & ?)] H; now unfold sat_ag, sat_a, sat_g in H.
    Qed.


    Lemma sat_ag_proj_left_cons :        
        forall tr i_tr m_tr o_tr m'_tr a x y, 
        (i_tr, m_tr, (o_tr, m'_tr)) = pgrm_trace_split tr ->
         (i_tr, a) = sat_ag_proj_left (tr, (a, x, y)).
    Proof.
        intros. destruct tr.
        - inversion H. now subst.
        - destruct i. destruct p,p0. rewrite pgrm_trace_split_cons in H. cbn in *. inversion H.
         unfold sat_ag_proj_left. f_equal.  unfold trace_to_input_trace. unfold pgrm_trace_split. cbn. destruct (split tr) eqn:X.
        cbn. now destruct (split l) eqn:Y.
    Qed. 


    Lemma sat_ag_proj_left_build_trace_history : 
        forall tr i_tr m_tr o_tr m'_tr , 
        (i_tr, m_tr, (o_tr, m'_tr)) = pgrm_trace_split tr ->
         build_trace_history i_tr = map sat_ag_proj_left (build_trace_history tr).
    Proof.

    induction tr.
    - intros. now inversion H.
    - intros. rewrite build_trace_history_cons. cbn. destruct a. destruct p , p0.
        pose proof H as Htr_split'.
        rewrite pgrm_trace_split_cons in H. cbn in *.
        apply pgrm_trace_split_inv in Htr_split' as (i_tr' & m_tr' & o_tr' & m'_tr' & Htr_split' & Hit & Hmt & Hotr & Hmt').
        subst. inversion H.
        unfold sat_ag_proj_left at 1.
        rewrite build_trace_history_cons. unfold sat_ag_proj_left at 1. cbn. f_equal. 
        f_equal. subst. specialize (IHtr _ _ _ _ Htr_split'). now inversion IHtr.
    Qed.


    Lemma sat_ag_proj_right_sat_g : forall (a : ag_aut_label) (b : pgrm_trace * instant), sat_ag a b -> 
        sat_g (snd a) (sat_ag_proj_right b).
    Proof.
        intros [? ?] [? ([? ?] & ? & ?)] H; now unfold sat_ag, sat_a, sat_g in H.
    Qed.


    Fact ag_aut_deterministic : aut_deterministic _ _ _ sat_a a_aut -> aut_deterministic _ _ _ sat_g g_aut -> aut_deterministic _ _ _ sat_ag ag_aut.
    Proof.
        unshelve eapply (prod_deterministic _ _ _ _ a_aut g_aut _ _ _ sat_ag 
            sat_a sat_ag_proj_left _ 
            sat_g sat_ag_proj_right _).
        - exact sat_ag_proj_left_sat_a.
        - exact sat_ag_proj_right_sat_g.
    Qed.


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
        postcond_to_precond (snd precond) tr i ->
        join_preds tr i m curr_n
    .  

    (* join_succs n pre tr i m o m' is the disjunction of all successors (pre',post) with a precondition equivalent to pre such post tr i m o m' *)
    Inductive join_succs curr_node pre tr i m o m' : Prop := 
    | join_succs_ pre' post next_n  :
        successor _ _ ag_aut next_n (pre',post) curr_node ->
        (pre' (trace_to_input_trace tr) i <-> pre (trace_to_input_trace tr) i) ->
        post tr (i,m) (o,m') ->
        join_succs curr_node pre tr i m o m'
    .  


    (* triple_gen t n pre tr i m o m' is the triple t generated for node n for the given precondition *)
    Inductive triple_gen (P: Program) (t: HoareTriple) curr_node pre tr i m o m' : Prop := 
    | triple_gen_cons :
        
        
        (* the triple precondition must be equivalent to the conjunction of the disjunction of previous postconditions and current precondition *)
        (   local_pre t tr i 
            <-> 
            (join_preds tr i m curr_node /\ pre (trace_to_input_trace tr) i)
        ) 
        ->
        
        (* the triple postcondition is the disjunction of all postconditions of successors nodes with equivalent precondition  *)
        (
            local_post t tr (i,m) (o,m') <-> join_succs curr_node pre tr i m o m'
        ) ->
        body t = loop P ->
        triple_gen P t curr_node pre tr i m o m'
    .


    (* each outgoing transition is associated with one more multiple triples *)
    Definition valid_generated_triples (P: Program) : Prop := 
        forall n , 
        reachable ag_aut n ->
        forall pre post next_n,  successor _ _ ag_aut next_n (pre,post) n  ->
        forall tr i m o m',
        exists t, triple_gen P t n pre tr i m o m' /\ valid_triple t tr i m o m'
    .

End Reduction.


Abbreviation ag_aut_node := (a_aut_node * g_aut_node)%type.
Abbreviation ag_aut_label  := (a_aut_label * g_aut_label)%type.

(* strengthened version of valid_contract to use for induction, where we keep track of the path in the automata *)
Definition valid_contract_wit (C: Contract) (P: Program): Prop := 
    (contract_setup C) (setup P) ->
    forall i m o m' tr, 
    run P (((i,m),(o,m'))::tr) ->
    forall i_tr m_tr o_tr m'_tr,
    ((i_tr,m_tr),(o_tr,m'_tr)) = pgrm_trace_split tr ->
    
    forall a_p a_curr_trans a_next_node, 
        language_wit sat_a (contract_assumes C) ((a_curr_trans,a_next_node)::a_p) (build_trace_history (i::i_tr)) -> 

    exists ag_p, left_proj ag_p = a_p /\        
    exists ag_curr_trans g_next_node, 
        language_wit sat_ag (ag_aut C) ((ag_curr_trans, (a_next_node, g_next_node))::ag_p) (build_trace_history (((i,m),(o,m'))::tr)) 
        (* /\ (fst ag_curr_trans i_tr i <-> a_curr_trans i_tr i) *)
.

Lemma valid_contract_wit_valid C P : valid_contract_wit C P -> valid_contract C P.
Proof.
    intros  Hvalid_wit Hvalid_setup tr Hrun i_tr m_tr [o_tr m'_tr] Hsplit Ha_lang.
    destruct Ha_lang as (a_path & Ha_path & Ha_path_valid). destruct a_path as [|[a_curr_label a_next_node] a_path].
    -   (* empty path -> empty trace -> trivially sat *)
        cbn in Ha_path_valid. inversion Ha_path_valid. symmetry in H; apply -> build_trace_history_iff_h_nil in H. subst. destruct tr eqn:X;[easy|].
        destruct i as [[i m] [o m']].
        pose proof  pgrm_trace_split_cons p i o m m'. unfold pgrm_trace_split in Hsplit, H. cbn in *. now rewrite H in Hsplit. 

    - destruct tr as [|[[i m] [o m']] tr];[easy|]. 
        pose proof Hsplit as Hsplit'.
        apply pgrm_trace_split_inv in Hsplit as (i_tl & m_tl & o_tl & m'_tl & Hsplit & Heq1 & Heq2 & Heq3 & Heq4); subst.
    
        specialize (Hvalid_wit Hvalid_setup _ _ _ _ _ Hrun _ _ _ _ Hsplit _ _ _ (conj Ha_path Ha_path_valid))
         as (ag_path & Hleft_proj & [a_curr_label' g_curr_label] & g_next_node & Hag_path_valid ). 
         rewrite build_trace_history_cons in *.
        inversion_clear Hag_path_valid as [Hag_path Hag_path_valid'];  cbn in *.
        exists ((g_curr_label,g_next_node)::right_proj ag_path); split. 
    
        + now apply path_right_proj in Hag_path.
        + apply valid_right_proj  with  (sat2:= sat_g) (transf2:=id) in Hag_path_valid'.
            * cbn in *. inversion Hag_path_valid'; subst; cbn in *. rewrite map_id in H2. constructor; [|assumption].
                replace (map fst (right_proj ag_path)) with (map snd (map fst ag_path));[assumption|].
                clear. induction ag_path; [reflexivity|simpl; f_equal; apply IHag_path].

            * intros * Hsat_ag. red in Hsat_ag. now destruct b as [tr' [[i0 m0 ] [o0 m'0]]].  
Qed.

Definition wf_a_aut C := aut_deterministic _ _ _ sat_a (a_aut C).
Definition wf_g_aut C := aut_complete _ _ (g_aut C).


Theorem correctness_aux P C: 
    wf_a_aut C -> 
    wf_g_aut C -> 
    valid_generated_triples C P -> 
    valid_contract_wit C P. 
Proof.
    intros Ha_aut_deterministic Hg_aut_complete  Htriples Hvalid_setup i m o m' tr.
     revert i m o m'. induction tr.  

    - intros i m o m' Hrun. (* first instant  *) 
        inversion Hrun as [? ? ? Hloop|].  subst.
        intros i_tr m_tr o_tr m'_tr Htr_split a_path a_curr_label a_next_node Ha_lang.
        inversion Htr_split; subst.
        rewrite build_trace_history_cons in Ha_lang |- *.


        (* get current a_aut transition *)
        inversion Ha_lang as (Ha_path & Ha_path_valid). 
        inversion Ha_path_valid as [|? ?  ? ? Ha_path_valid_prev Ha_curr_valid]; subst.
        destruct a_path; [|easy].
        
        (* moreover, we have a transition in the assumes automaton from the initial node to a_n *)
        inversion Ha_path as [x|? ? Ha_trans x|x]; subst.
        exists nil. split; [now constructor|]. 
        
        (* we have a transition in ag_aut from the initial node to (a_n,g_n) *)
        assert (exists (g_curr_label : g_aut_label) g_next_node,
                        transition (ag_aut C) (init (ag_aut C)) (a_curr_label, g_curr_label) (a_next_node,g_next_node)) 
        as (g_curr_label & g_next_node & Hag_trans).
        {
                assert (reachable (g_aut C) (init (g_aut C))) as H_reach by (left; reflexivity).
                destruct (Hg_aut_complete (init (g_aut C)) H_reach) as [g [g_n H_trans]].
                exists g, g_n; easy.
        }
        
        (* this transition is reachable by definition *)
        assert (Hinitreach : reachable (ag_aut C) (init (a_aut C), init (g_aut C))) by now constructor.

        (* we get the our triple *)
        specialize (Htriples _ Hinitreach _ _ _ Hag_trans nil i (setup P) o m') as (t & Htriples_gen & Htriples_valid);
        destruct Htriples_gen as [Hpre Hpost Ht_body].

        rewrite <- Ht_body in Hloop .
        
        (* no predecessors when this is the first instant *)
        assert (Hpreds : join_preds C nil i (setup P) (init (a_aut C), init (g_aut C))) by now constructor.

        (* we have the hypothesis that makes our precondition hold *)
        pose proof (conj Hpreds Ha_curr_valid) as Hpre'; apply <- Hpre in Hpre'.
        
        (* our triple validity implies local_post holds *)
        specialize (Htriples_valid Hpre' Hloop).
        
        (* this gives us the condition on the transitions *)
        apply Hpost in Htriples_valid; inversion Htriples_valid as [? ? [a_next_node' g_next_node'] Hsucc Hpre_equiv Hpost_valid].

        (* pre' is a_curr_label and next_n is (a_next_node,g_next_node) because of determinism *)
        assert (Heq : pre' = a_curr_label /\  a_next_node' = a_next_node ). {
            assert (Ha_lang':  language_wit sat_a (a_aut C) ((pre',a_next_node')::nil) ((nil, i) :: build_trace_history nil)). {
                inversion Hsucc as [Ha_succ _]; cbn in Ha_succ.
                constructor;[now constructor |constructor; [constructor|now apply Hpre_equiv]].
            }

            pose proof (aut_deterministic_eq _ _ _ _ _ Ha_aut_deterministic _ _ _ Ha_lang Ha_lang') as H. now inversion H.
        }

        destruct Heq. subst.


        exists (a_curr_label,post), g_next_node'. split; [now constructor|constructor; [constructor|]].
        split; cbn; [now rewrite Hpre_equiv|assumption].

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
        specialize (IHtr _ _ _ Ha_lang_prev) as (ag_path & Hag_path_left & (a_prev_label', g_prev_label) & g_curr_node & Hag_lang_prev).
        rewrite build_trace_history_cons in *.
        
        (* we extract the left and right paths *)
        pose proof language_left_proj _ _ _ _ _ _ _ _ _ _ _ sat_ag_proj_left_sat_a _ _  Hag_lang_prev as Hag_lang_left;
        pose proof language_right_proj _ _ _ _ _ _ _ _ _ _ _ sat_ag_proj_right_sat_g _ _  Hag_lang_prev as Hag_lang_right;
        cbn in Hag_lang_left, Hag_lang_right. 


        (* we show the left path in the product automaton must be the same as our assumes automaton path *)
        erewrite <- sat_ag_proj_left_build_trace_history in Hag_lang_left; [|eauto];
        erewrite <- sat_ag_proj_left_cons in Hag_lang_left; [|eauto].
        pose proof (aut_deterministic_eq _ _ _ _ _ Ha_aut_deterministic  _ _ _ Hag_lang_left Ha_lang_prev) as Heq. inversion Heq; subst. clear Heq H1.


        inversion Ha_path as [X|?|? ? ? ? ?  _ Ha_trans]; subst.
    

        (* we extend the product automaton with the current assumption transition *)
        inversion Hag_lang_prev as [Hag_path_prev Hag_valid_prev]. cbn in Hag_path_prev, Hag_valid_prev.
        assert (Hag_curr_reach: reachable (ag_aut C) (a_curr_node, g_curr_node)) by (constructor 2; eauto).
        apply reachable_right_proj in Hag_curr_reach as Hnext_g; cbn in Hnext_g; apply Hg_aut_complete in Hnext_g as (g_curr_label & g_next_node & Hg_trans).

        assert (Hag_trans: successor ag_aut_node ag_aut_label (ag_aut C) (a_next_node, g_next_node) (a_curr_label, g_curr_label) (a_curr_node, g_curr_node)) by exact (conj Ha_trans Hg_trans).
        specialize (Htriples _ Hag_curr_reach _ _ _ (Hag_trans) ((prev_i, prev_m, (prev_o, m)) :: tr) i m o m') as (t & Htriple_gen & Hvalid_triple).

        destruct Htriple_gen as [Ht_pre Ht_post Ht_body ].

        (* we now construct the hypotheses to satisfy Ht_pre... *)

        assert (Hpreds: join_preds C ((prev_i, prev_m, (prev_o, m)) :: tr) i m (a_curr_node, g_curr_node)). {
            inversion Hag_path_prev; subst.
            + apply (join_preds_cons _ _ _ _ (init (ag_aut C)) (a_prev_label,g_prev_label) (a_curr_node,g_curr_node)).
                * apply H0.
                * cbn. inversion Hag_valid_prev; subst. now inversion H5.
            + apply (join_preds_cons _ _ _ _ m0 (a_prev_label,g_prev_label) (a_curr_node,g_curr_node)).
                * assumption.
                * cbn. inversion Hag_valid_prev; subst. apply H6.
        }

        assert (Hitrace : (prev_i :: i_tr) = (trace_to_input_trace ((prev_i, prev_m, (prev_o, m)) :: tr))). {
            unfold trace_to_input_trace. rewrite pgrm_trace_split_cons. cbn. now inversion Htr_split.
        }

        rewrite Hitrace in Ha_curr.
        pose proof (conj Hpreds Ha_curr) as Ht_pre'; apply Ht_pre in Ht_pre'; clear Ht_pre.

        (* ...and we use it to obtain our join_succs hypothesis *)
        rewrite <- Ht_body in Hloop; specialize (Hvalid_triple Ht_pre' Hloop); apply Ht_post in Hvalid_triple.

        (* by determinism of the assumption automaton, this is our current assumption *)
        inversion Hvalid_triple.  apply H0 in Ha_curr as Ha_curr_sat'; clear H0.
        destruct Ha_aut_deterministic as [_ Had]. cbn in Had. 
        destruct (Had _ _ _ _ _ _ _ _ Ha_lang_prev (conj Ha_trans Ha_curr) (conj (proj1 H) Ha_curr_sat')) as [Heq_trans Heq_node]; cbn in Heq_trans, Heq_node; symmetry in Heq_trans, Heq_node; subst.

        exists (((a_prev_label, g_prev_label),(a_curr_node,g_curr_node))::ag_path); split; [reflexivity|].
        exists (a_curr_label, post), (snd next_n). cbn. split; [now constructor|]. now constructor.
Qed.


Corollary correctness P C : 
    wf_a_aut C -> 
    wf_g_aut C -> 
    valid_generated_triples C P -> 
    valid_contract C P. 
Proof.
    intros Ha_wf Hg_wf Hvalid. apply valid_contract_wit_valid; apply correctness_aux; assumption.
Qed.
