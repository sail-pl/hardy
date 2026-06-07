From Hardy Require Import automaton product.
From Stdlib Require Import List Ensembles.


Parameter input output mem : Type.

Definition instant : Type := nat.

Definition trace {A} : Type := list A.
Definition trace_prefixes {A : Type} : Type := @trace (@trace A * A). 


Abbreviation input_trace := (@trace input).
Abbreviation output_trace := (@trace output). 
Abbreviation mem_trace := (@trace mem). 


(* 
    given a new input i and with current memory mem, the program produced the output o
    the new memory correspond to the next element in the list.

    last output is the first element of the list

    an element ((i,m)(o,m')) of a trace represent the memory m' and output o produced by the program after receiving input i and memory m

    invariant : m must be the same as previous m'
*)
Definition private_trace : Type := @trace ((input*mem)*(output*mem)). 
Definition public_trace : Type := @trace (input*output). 


Definition private_trace_split : private_trace -> (input_trace * mem_trace) * (output_trace * mem_trace)  := fun tr =>
    (List.split (fst (List.split tr)), List.split (snd (List.split tr))).

Definition private_to_input_trace : private_trace -> input_trace := fun tr =>  
    fst (fst (private_trace_split tr)).

Definition private_trace_combine : (input_trace * mem_trace) * (output_trace * mem_trace) -> private_trace := fun '((i,m),(o,m')) =>
    List.combine (List.combine i m) (List.combine o m').

Lemma private_trace_split_cons tr i o m m' : 
    private_trace_split (((i,m),(o,m')):: tr) = 
    (
        (
            i ::fst (fst (private_trace_split tr)), 
            m :: snd (fst (private_trace_split tr))
        ),
        (
            o :: fst (snd (private_trace_split tr)),
            m' :: snd (snd (private_trace_split tr))
        )
    )
.
Proof.
Admitted.


Lemma private_trace_split_inv tr i m o m' i_t m_t o_t m_t' : 
    ((i_t, m_t), (o_t, m_t')) = private_trace_split (((i,m),(o,m')):: tr)
    <-> (
    exists i_tl m_tl o_tl m_tl',
    ((i_tl,m_tl), (o_tl,m_tl')) = private_trace_split tr /\
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
Admitted.


Lemma split_combine_trace t : t = private_trace_combine (private_trace_split t).
Proof.
    induction t.
    - easy.
    - unfold private_trace_combine, private_trace_split in *; cbn.
        destruct (split t) as [im om'] eqn:Heq_t; cbn.
        pose proof length_fst_split im as Hi; pose proof length_snd_split im as Hm. 
        pose proof length_fst_split om' as Ho; pose proof length_snd_split om' as Hm'. 
        destruct (split im) as [i m] eqn:Heq_im; cbn in *.
        destruct (split om') as [o m'] eqn:Heq_om'; cbn in *.
        destruct a as ((a_i,a_m),(a_o,a_m')) eqn:Heq2. cbn.  
        destruct (split im) eqn:Hbla; destruct (split om') eqn:Hbla'; cbn; subst. now inversion Heq_om'. 
Qed.

Lemma combine_split_trace (i_t: input_trace) (m_t m_t': mem_trace) (o_t : output_trace) :
    List.length i_t = List.length m_t /\
    List.length m_t = List.length m_t'/\
    List.length o_t = List.length m_t 
    ->
    ((i_t,m_t),(o_t, m_t')) = private_trace_split (private_trace_combine ((i_t,m_t),(o_t,m_t'))).
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
        unfold private_trace_split in *.
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

(* Fact build_trace_history_inv : forall A tr p x tr', 
    (tr', x) :: p = @build_trace_history A tr ->
    exists tr_tl, 
    tr = x::tr_tl /\ tr = tr'.
Proof.
    induction tr.
    - discriminate.
    - intros tr' x p H.  rewrite build_trace_history_cons in H. inversion H; subst; clear H.
         discriminate. inversion H1.
        inversion 
     specialize (IHtr _ _ _ H). cbn. cbn.
    induction H.
    induction tr; intro h; simpl in *.
    - reflexivity.
    - now rewrite IHtr at 1 2.
Qed. *)



Definition f : Type := input * mem -> output * mem.

Record Program : Type := {
    setup: unit -> mem;
    loop: f;
}.

(* run m l is the trace produced by the program where m is the first memory state  *)
Inductive run (P : Program) : mem -> private_trace -> Prop :=
    | run_start i o m' : 
        loop P (i,(setup P tt)) = (o,m') ->
        run P (setup P tt) (((i,(setup P tt)),(o,m'))::nil)
    
    | run_next tr mem_init prev_i prev_o prev_m i o m m' : 
        run P mem_init (((prev_i, prev_m), (prev_o, m))::tr) ->
        loop P (i,m) = (o,m') ->
        run P mem_init (((i,m),(o,m'))::((prev_i, prev_m),(prev_o, m))::tr)
.

Fact run_m_m' (P: Program ) mem_init tr prev_i prev_o prev_m i m o m' : 
    run P mem_init (((i,m),(o,m'))::((prev_i,m),(prev_o,prev_m))::tr) -> 
    prev_m = m 
.
Proof.
    intros H. now inversion H.
Qed.

(* property made up of the history of previous inputs, states and outputs and current input and mem *)
Definition local_precond : Type :=  private_trace -> (input*mem) -> Prop.
Definition local_postcond : Type :=  private_trace -> (input*mem) -> (output*mem) -> Prop.



(* hardy's output: hoare triples *)
Record HoareTriple : Type := mkTriple {
    local_pre : local_precond;
    body : f;
    local_post : local_postcond;
}.

(* what the deductive verifier proves for each triple *)
Definition valid_triple (T:HoareTriple)  : Prop := 
    forall t i m o m',
    local_pre T t (i,m) -> 
    body T (i,m) = (o,m') ->
    local_post T t (i,m) (o,m')  
.


Definition aut_complete {N L} (a: automaton N L): Prop := 
    forall n, reachable a n -> exists p m, transition a n p m.


(* Definition aut_node_dec {N L} (a: automaton N L) (n1 n2 :N) : Prop := n1=n2 \/ n1 <> n2.


Fact prod_aut_node_dec {N1 N2 L1 L2} (a1: automaton N1 L1) (a2: automaton N2 L2) (n m :N1*N2) :  
    aut_node_dec a1 (fst n) (fst m) ->
    aut_node_dec a2 (snd n) (snd m) ->
    aut_node_dec (product a1 a2) n m.
Proof.
    destruct n as  [n1 n2], m as [m1 m2]. intros Hdec1 Hdec2; cbn in *.  inversion Hdec1; inversion Hdec2; subst.
    1: now left.
    1,2,3: right; intros Hcontra; try now inversion Hcontra.
Qed.

 *)



(* 'assumes' automata transition label: predicate on previous inputs and current input *)
Definition a_aut_label : Type := @trace input -> input -> Prop.

Definition sat_a (p: a_aut_label) '((t,i): @trace input * input) : Prop := p t i.


(* 'guarantees' automata transition label: predicate on trace history, current input and memory, and next output and memory  *)
Definition g_aut_label : Type :=  private_trace -> (input*mem) -> (output*mem) -> Prop.

Definition sat_g (p: g_aut_label) '((t,(im,om')): @private_trace * ((input * mem) * (output * mem))) : Prop :=
    p t im om'.


Parameter a_aut_node : Type.

Parameter g_aut_node : Type.


(* hardy's input: temporal contracts defined as büchi automata *)
Record Contract : Type := {
    contract_setup : mem -> Prop;
    contract_assumes : automaton a_aut_node a_aut_label;
    contract_guarantees : automaton g_aut_node g_aut_label;
}.


(* given a stream of inputs accepted by a_aut, the program always produces a stream of outputs accepted by g_aut *)
Definition valid_contract (C: Contract) (P: Program): Prop := 
    (contract_setup C) (setup P tt) ->
    forall t m_init, 
    run P m_init t ->
    forall i_t m_t o_t,
    (i_t,m_t,o_t) = private_trace_split t ->
    language sat_a (contract_assumes C) (build_trace_history i_t) -> 
    language sat_g (contract_guarantees C) (build_trace_history t)
.


Section Reduction.
    Variable P : Program.
    Variable C : Contract.

    Definition a_aut := contract_assumes C.
    Definition g_aut := contract_guarantees C.


    Parameter a_aut_complete : aut_complete a_aut.
    Parameter g_aut_complete : aut_complete g_aut.

    
    Abbreviation ag_aut_node := (a_aut_node * g_aut_node)%type.
    Abbreviation ag_aut_label  := (a_aut_label * g_aut_label)%type.

    Definition ag_aut : automaton ag_aut_node ag_aut_label := product (contract_assumes C) (contract_guarantees C).

    Definition sat_ag (l: ag_aut_label) '((t,((i,m),(o,m'))): @private_trace * ((input * mem) * (output * mem))): Prop :=
        sat_a (fst l) (private_to_input_trace t,i) /\ 
        sat_g (snd l) (t,((i,m),(o,m')))
    .


    Lemma ag_aut_complete : 
        forall n, reachable ag_aut n -> 
            exists g m, transition ag_aut n g m.
    Proof.
        intros.
        assert (reachable_from (contract_assumes C) (init (contract_assumes C)) (fst n)).
        {
            destruct n.
            simpl.
            apply reachable_left_proj in H.
            apply H.
        }
        assert (reachable_from g_aut (init g_aut) (snd n)).
        {
            destruct n.
            apply reachable_right_proj in H.  
            apply H.
        }
        apply a_aut_complete in H0 as [f [n1 Ha]].
        apply g_aut_complete in H1 as [g [m1 Hb]].
        exists (f,g), (n1,m1).
        split; assumption.
    Qed.

    
    Definition postcond_to_precond (post: local_postcond) : local_precond := fun t => match t with
    | nil => fun _ => True (* no history *)
    | prev_inst::h =>  fun _ => 
        post h (fst (fst prev_inst), snd (fst prev_inst)) (fst (snd prev_inst), snd (snd prev_inst))
    end.


    Definition pre_meet (P1 : local_precond) (P2 : local_precond) : local_precond := 
        fun t c => P1 t c /\ P2 t c.

    Definition post_meet (Q1 : local_postcond) (Q2 : local_postcond) : local_postcond := 
        fun t c n => Q1 t c n /\ Q2 t c n.


    Definition pre_join (P1 : local_precond) (P2 : local_precond) : local_precond := 
        fun t c => P1 t c \/ P2 t c.

    Definition post_join (Q1 : local_postcond) (Q2 : local_postcond) : local_postcond := 
        fun t c n => Q1 t c n \/ Q2 t c n.

    (* Definition pre_equiv (P1: local_precond) (P2 : local_precond) : local_precond :=
        fun t c => P1 t c <-> P2 t c. *)

    (* Definition post_equiv (Q1 : local_postcond) (Q2 : local_postcond) : local_postcond := 
        fun t c n => Q1 t c n <-> Q2 t c n.
     *)
    Definition pre_setup : local_precond := fun t '(i,m) => t = nil /\ contract_setup C m.



    (* disjunction of all possible postconditions of previous transition converted into precondition.
        if the node is initial, add the setup to the disjunction
    *)
    Inductive join_preds (a: automaton ag_aut_node ag_aut_label) (n: ag_aut_node) : Ensemble _ -> local_precond -> Prop :=
    | join_preds_setup precond curr_preds: 
        n = init a ->
        join_preds a n curr_preds precond ->
        join_preds a n curr_preds (pre_join pre_setup precond)

    |  join_preds_one pred : 
        predecessors _ _ a (Singleton _ pred) n ->
        join_preds a n (Singleton _ pred) (fun t '(i,m) => postcond_to_precond (snd (snd pred)) t (i,m))


    | join_preds_cons precond curr_preds preds p : 
        join_preds a n curr_preds precond ->
        predecessors _ _ a preds n -> 
        In _ preds p -> 
        join_preds a n (Add _ curr_preds p) (pre_join precond (postcond_to_precond (snd (snd p))))
    .

    


    Inductive triple_gen (a: automaton ag_aut_node ag_aut_label) (t: HoareTriple) : ag_aut_node -> Prop := 
    | triple_gen_ preds preds_cond n succs :
        join_preds a n preds preds_cond  ->
        successors _ _ a n succs ->
        (
            forall succ, In _ succs succ ->
            let '((pre_succ,post_succ),_) := succ in 

            forall tr i m o m',

            (local_pre t tr (i,m) <->
                (pre_meet 
                    (* postcondition from the predecessor becomes precondition for the current node *)
                    preds_cond
                    (* add the precondition provided by the current successor *)
                    (fun t '(i,m) => pre_succ (private_to_input_trace t) i)) tr (i,m))

                
            /\ 

            (local_post t tr (i,m) (o,m') <-> post_succ tr (i,m) (o,m'))

            /\
            body t = loop P
        ) ->
        triple_gen a t n
        .


    Definition valid_generated_triples : Prop := forall n, 
        reachable ag_aut n ->
        exists t, 
        triple_gen ag_aut t n /\
        valid_triple t.

End Reduction.


Abbreviation ag_aut_node := (a_aut_node * g_aut_node)%type.
Abbreviation ag_aut_label  := (a_aut_label * g_aut_label)%type.

Definition valid_contract_wit (C: Contract) (P: Program): Prop := 
    (contract_setup C) (setup P tt) ->
    forall t last_mem, 
    run P last_mem t ->
    forall i_tr m_tr o_tr m'_tr,
    ((i_tr,m_tr),(o_tr,m'_tr)) = private_trace_split t ->
    forall a_p, language_wit sat_a (contract_assumes C) a_p (build_trace_history i_tr) -> 
    exists ag_p, 
        left_proj ag_p = a_p /\
        language_wit sat_ag (ag_aut C) ag_p (build_trace_history t)
.

Lemma valid_contract_wit_valid C P : valid_contract_wit C P -> valid_contract C P.
Proof.
    intros  Hvalid_wit Hvalid_setup t last_mem Hrun i_tr m_tr [o_tr m'_tr] Hsplit Ha_lang.
    destruct Ha_lang as (a_path & Ha_path & Ha_path_valid).
    specialize (Hvalid_wit Hvalid_setup t last_mem Hrun i_tr m_tr o_tr m'_tr Hsplit a_path (conj Ha_path Ha_path_valid))
         as (ag_path & Hag_p_a & Hag_path & Hag_path_valid).
    exists (right_proj ag_path); split.
    - now apply path_right_proj in Hag_path.
    - eapply valid_right_proj  with  (sat:= sat_g) (transf:=id) in Hag_path_valid.
        + replace (map fst (right_proj ag_path)) with (map snd (map fst ag_path)).
            ++ now rewrite map_id in Hag_path_valid.
            ++ clear. induction ag_path; [reflexivity|simpl; f_equal; apply IHag_path].
        + intros * Hsat_ag. red in Hsat_ag. destruct b as [t'  ([i m] & [o m'])]. now apply Hsat_ag. 
Qed.



Theorem correctness_aux P C : 
    valid_generated_triples P C -> 
    valid_contract_wit C P. 
Proof.
    intros Hval.
    red in Hval.
    intros Hvalid_setup tr m' Hrun. induction Hrun.

    - (* first instant  *) 
        intros i_tr m_tr o_tr m'_tr Htr_split a_path Ha_lang.
        inversion Htr_split; subst.
        rewrite build_trace_history_cons in Ha_lang |- *.


        (* now, we place ourselves onto the initial node of ag, which is reachable by definition *)
        assert (Hinitreach : reachable (ag_aut C) (init (a_aut C), init (g_aut C))) by now constructor.
        specialize (Hval _ Hinitreach).

        (* get current a_aut transition *)
        inversion Ha_lang as (Ha_path & Ha_path_valid) ;
        destruct a_path as [ | [a_curr_label a_next_node] a_path]; [ inversion Ha_path_valid |].

        inversion Ha_path_valid as [|? ?  ? ? Ha_path_valid_prev Ha_curr_valid]; subst.
        destruct a_path; [|easy].
        
        (* moreover, we have a transition in the assumes automaton from the initial node to a_n *)
        inversion Ha_path as [x|? ? Ha_trans x|x]; subst.

        (* we now show we also have a transition in ag_aut from the initial node to (a_n,g_n) such that
        its right component g_postcond satisfy the program first postcondition  *)
        assert (exists g_curr_label g_next_node, 
            transition (ag_aut C) (init (a_aut C), init (g_aut C)) (a_curr_label,g_curr_label) (a_next_node, g_next_node) /\ 
            g_curr_label nil (i,setup P tt) (o, m')
        ) as (g_curr_label & g_next_node & [ag_aut_trans Hg_n]).
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

            (* we now show the right element of the transition is the right postcondition *)
                            
            
            (* let's have look at our triple for the current node *)
            destruct Hval as (t & Ht & Htvalid).
            inversion_clear Ht as [preds precond Hpreds succs Hjpreds Hsuccs Ht' X].

            (* init node with the setup *)
            -   assert (Hin_ag_succ : In _ succs (a_curr_label, g_curr_label, (a_next_node, g_next_node))) by now apply Hsuccs in Hag_trans.

                (* we obtain its content *)
                specialize (Ht' (a_curr_label, g_curr_label, (a_next_node, g_next_node)) Hin_ag_succ nil i (setup P tt) o m') as (Ht_pre & Ht_post & Ht_body).

                (* this gives us the postcondition *)
                rewrite <- Ht_post; apply Htvalid; [|now rewrite Ht_body]. 
                rewrite Ht_pre; unfold pre_meet, pre_join; cbn; split; [|assumption].
                inversion Hjpreds.
                + now left.
                + now cbn.
                + now right.
        }

        exists (((a_curr_label,g_curr_label), (a_next_node,g_next_node))::nil). split; [reflexivity|].

        split.
        *  exact (path_transition _ _ _ _ _ _ ag_aut_trans).
        *  assert (Hag_sat : sat_ag (a_curr_label, g_curr_label) (nil, ((i,setup P tt,(o, m')))))
                by easy.
            exact (valid_cons _ _ _ _ _ _ _ (valid_nil _ _ _) Hag_sat).


    -  (* nth instant *)
        intros i_tr m_tr o_tr m'_tr Htr_split a_path Ha_lang. 
        apply (private_trace_split_inv ( (prev_i, prev_m, (prev_o, m)) :: tr) i m o m' i_tr m_tr o_tr m'_tr) in Htr_split 
            as  (i_tr' & m_tr' & o_tr' & m'_tr' & Htr_split & Hit & Hmt & Hotr & Hmtr); subst.
        rename i_tr' into i_tr, o_tr' into o_tr, m_tr' into m_tr;
        rewrite build_trace_history_cons in Ha_lang |- *.
        
        (* get current a_aut transition *)
        inversion Ha_lang as (Ha_curr_path & Ha_curr_path_valid) ;
        destruct a_path as [ | [a_curr_label a_next_node] a_path]; [ inversion Ha_curr_path_valid |]. 
        
        assert (Ha_lang_prev : language_wit sat_a (contract_assumes C) a_path (build_trace_history i_tr) ) by
        now apply language_prefix_closed with (h := (a_curr_label, a_next_node)) (a :=(i_tr, i) ).

        inversion Ha_curr_path_valid as [|? ?  ? ? Ha_path_valid_prev Ha_curr_valid]; subst.

        

        (* our induction hypothesis gives us a path in the product automaton 
            that contains the path from the assumption automaton, but with one less transition
            such that the trace up to the previous instant is valid
        *)
        specialize (IHHrun _ _ _ _ Htr_split a_path Ha_lang_prev); clear Ha_lang_prev; move IHHrun at bottom;
        destruct IHHrun as (ag_path & Hag_path_left_a & Hag_lang).
        rewrite build_trace_history_cons  in *.

        destruct ag_path as [|((a_prev_label & g_prev_label) & a_curr_node & g_curr_node) ag_path]; [now inversion Hag_lang|]; subst.

        inversion Ha_curr_path as [|?|? ? ? ? ? Ha_path Ha_trans X]; subst.


        apply (private_trace_split_inv tr prev_i prev_m prev_o m i_tr m_tr o_tr) in Htr_split as 
        (i_tr' & m_tr' & o_tr' & m'_tr'' & Htr_split & Hit & Hmt & Hot & Hm't); subst;
        rename i_tr' into i_tr, o_tr' into o_tr, m_tr' into m_tr, m'_tr'' into m'_tr'; rewrite build_trace_history_cons in *;
        cbn in *. 
        

        inversion Hag_lang as [Hag_path Hag_path_valid] ; subst;
            inversion Hag_path_valid as [X Hcontra | [tr'  [[prev_i' prev_m'] prev_o']] prev_ag_path ag_trans ag_m Hag_valid_prev_tr Hag_trans Hag_prev_path H_hist]; subst.

        cbn in Hag_trans; destruct Hag_trans as [ Ha_prev_valid Hg_prev_valid ].
        


        (* current node in the product is reachable *)
        assert (Hag_curr_reach: reachable (ag_aut C) (a_curr_node, g_curr_node)). {
                right. exists (a_prev_label, g_prev_label). 
                now exists ag_path.
        }

        (* this means we have generated triples for it *)
        destruct (Hval (a_curr_node, g_curr_node) Hag_curr_reach) as (curr_t & Hcurr_t & Hcurr_t_valid).


        (* we have a transition in ag_aut from the current node to the next whose left projection is a_curr_node  *)
        assert (exists (g_curr_label : g_aut_label) g_next_node,
                        transition (ag_aut C) (a_curr_node,g_curr_node) (a_curr_label, g_curr_label) (a_next_node,g_next_node))
        as (g_curr_label & g_next_node & Hag_trans_next).
        {
            (* this is because the product contains a path in g_aut g_curr_node and g_aut is complete *)
            assert (Hg_reach_m : reachable (g_aut C) g_curr_node) by (now apply reachable_right_proj in Hag_curr_reach).
            pose proof (g_aut_complete _ _ Hg_reach_m) as (g_curr_label & g_next_node & Hg_trans). 
            now  exists g_curr_label, g_next_node.
        }

        cbn in  Hag_trans_next; destruct Hag_trans_next as [ _ Hg_trans ].

        inversion_clear Hcurr_t as [preds precond Hpreds succs' Hjpreds Hsuccs Ht' X].
        

        (* instantiate the triple for this transition *)
        assert (Hin_ag_succ : In _ _ ((a_curr_label,g_curr_label),(a_next_node,g_next_node))) by (now apply Hsuccs);
        specialize (Ht' _ Hin_ag_succ ((prev_i, prev_m, (prev_o, m))::tr) i m o m') as (Hcurr_t_pre & Hcurr_t_post & Hcurr_t_body).
        

        exists (((a_curr_label,g_curr_label), (a_next_node,g_next_node))::((a_prev_label,g_prev_label), (a_curr_node,g_curr_node))::ag_path).
        split; [reflexivity|].
        

        split; cbn.

        + now constructor.
        + constructor; [now constructor|]; split; cbn.
            * unfold private_to_input_trace; rewrite private_trace_split_cons; cbn; subst.
                now  inversion_clear Htr_split; cbn.
                
            *  rewrite <- Hcurr_t_post.
                apply Hcurr_t_valid; [|now rewrite Hcurr_t_body ]; clear Hcurr_t_body.
                rewrite Hcurr_t_pre. unfold pre_meet, pre_join; cbn. split.
                -- induction Hjpreds as [prev_label preds Hinit Hjpreds IHHjpreds|([a_prev_node g_prev_node] & a_prev_label' & g_prev_label') Hpreds|a]; subst; cbn.
                    (* [   
                        prev_label preds Hjpreds IHHjpreds
                        | ([a_prev_node g_prev_node] & a_prev_label' & g_prev_label') (a_curr_node', g_curr_node') Hpreds
                        | [a_prev_node g_prev_node] prev_label preds pred ([a_prev_node' g_prev_node'] & a_prev_label' & g_prev_label')
                    ] *)
                    ++ right. apply IHHjpreds. split.
                        ** intros H'. apply Hcurr_t_pre in H'; inversion_clear H'; split; [|assumption].  
                            inversion_clear H0; [|assumption]. now cbn in H2.      
                        ** intros H'. apply Hcurr_t_pre. inversion_clear H'; split; [|assumption]. now right.

                    ++ specialize (Hpreds (a_prev_label', g_prev_label') (a_prev_node, g_prev_node)).
            
                        assert (Hin: In _ (Singleton _ (a_prev_node, g_prev_node, (a_prev_label', g_prev_label'))) (a_prev_node, g_prev_node, (a_prev_label', g_prev_label'))) by constructor; 
                        apply Hpreds in Hin as [Hag_prev_reach Hag_prev_trans].
                        destruct (Hval (a_prev_node, g_prev_node) Hag_prev_reach) as (prev_t & Hprev_t & Hprev_t_valid).
                        inversion_clear Hprev_t as [ag_prev_node_preds ag_prev_label ag_prev_node_succs Hag_prev_node_preds Hag_prev_node_succs Hsuccs' Hprev_t_]; 
                        rename Hprev_t_ into Hprev_t.
                        assert (Hin_ag_prev: In _ ag_prev_node_succs (a_prev_label', g_prev_label', (a_curr_node, g_curr_node))) by admit.
                    specialize (Hprev_t _ Hin_ag_prev) as (Hprev_t_pre & Hprev_t_post & Hprev_t_body).

                    rewrite <- Hprev_t_post. apply Hprev_t_valid.
                    ++ rewrite Hprev_t_pre. unfold pre_meet, pre_join; cbn. split.
                        ** right.  intros *. admit.
                        ** admit.
                    ++ rewrite Hprev_t_body. now inversion Hrun. 


                    ++ specialize (IHHjpreds Hag_lang Hag_path Hag_path_valid Hag_curr_reach Hsuccs).
                        left. apply IHHjpreds. split.
                        ** intros H'. apply Hcurr_t_pre in H'; inversion_clear H'; split; [|assumption].
                            inversion_clear H2; [assumption|]. cbn in H4. admit.
                        ** intros H'. apply Hcurr_t_pre. inversion H'; split; [|assumption]. now left.

                
                    (* right. intros (ag_prev_node & a_prev_label' & g_prev_label') Hincurr_preds.
                    (* we must show the postcondition becomes the precondition *)

                    assert (Hag_prev_reach: reachable (ag_aut C) ag_prev_node)
                        by now apply Hag_curr_node_preds in Hincurr_preds.

                    destruct (Hval ag_prev_node Hag_prev_reach) as (prev_t & Hprev_t & Hprev_t_valid).
                    inversion_clear Hprev_t as [ag_prev_node_preds ag_prev_node_succs Hag_prev_node_preds Hag_prev_node_succs Hprev_t_]; 
                    rename Hprev_t_ into Hprev_t.
                    assert (Hin_ag_prev: In _ ag_prev_node_succs (a_prev_label', g_prev_label', (a_curr_node, g_curr_node))) by admit.
                    specialize (Hprev_t _ Hin_ag_prev) as (Hprev_t_pre & Hprev_t_post & Hprev_t_body).

                    rewrite <- Hprev_t_post. apply Hprev_t_valid.
                    ++ rewrite Hprev_t_pre. unfold pre_meet, pre_join; cbn. split.
                        ** right.  intros *. admit.
                        ** admit.
                    ++ rewrite Hprev_t_body. now inversion Hrun.  *)

                    
                -- unfold private_to_input_trace; rewrite private_trace_split_cons; cbn; subst.
                     now inversion_clear Htr_split; cbn.
Admitted.


Corollary correctness P C : 
    valid_generated_triples P C -> 
    valid_contract C P. 
Proof.
    intros Hvalid; apply valid_contract_wit_valid; apply correctness_aux; assumption.
Qed.
