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



Parameter input output mem : Type.


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
Definition pgrm_trace : Type := @trace ((input*mem)*(output*mem)). 

Definition pgrm_trace_split : pgrm_trace -> (input_trace * mem_trace) * (output_trace * mem_trace)  := fun tr =>
    (List.split (fst (List.split tr)), List.split (snd (List.split tr))).

Definition private_to_input_trace : pgrm_trace -> input_trace := fun tr =>  
    fst (fst (pgrm_trace_split tr)).

Definition pgrm_trace_combine : (input_trace * mem_trace) * (output_trace * mem_trace) -> pgrm_trace := fun '((i,m),(o,m')) =>
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

Lemma combine_split_trace (i_t: input_trace) (m_t m_t': mem_trace) (o_t : output_trace) :
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

Definition f : Type := input * mem -> output * mem.

Record Program : Type := {
    setup: unit -> mem;
    loop: f;
}.

(* run m l is the trace produced by the program where m is the first memory state  *)
Inductive run (P : Program) : pgrm_trace -> Prop :=
    | run_start i o m' : 
        loop P (i,(setup P tt)) = (o,m') ->
        run P (((i,(setup P tt)),(o,m'))::nil)
    
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

(* property made up of the history of previous inputs, states and outputs and current input and mem *)
Definition local_precond : Type :=  pgrm_trace -> (input*mem) -> Prop.
Definition local_postcond : Type :=  pgrm_trace -> (input*mem) -> (output*mem) -> Prop.



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


Definition aut_complete {N L} (a: automaton N L): Prop := 
    forall n, reachable a n -> exists p m, transition a n p m.


(* 'assumes' automata transition label: predicate on previous inputs and current input *)
Definition a_aut_label : Type := @trace input -> input -> Prop.

Definition sat_a (p: a_aut_label) '((t,i): @trace input * input) : Prop := p t i.


(* 'guarantees' automata transition label: predicate on trace history, current input and memory, and next output and memory  *)
Definition g_aut_label : Type :=  pgrm_trace -> (input*mem) -> (output*mem) -> Prop.

Definition sat_g (p: g_aut_label) '((t,(im,om')): @pgrm_trace * ((input * mem) * (output * mem))) : Prop :=
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
    forall t, 
    run P t ->
    forall i_t m_t o_t,
    (i_t,m_t,o_t) = pgrm_trace_split t ->
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

    Definition sat_ag (l: ag_aut_label) '((t,((i,m),(o,m'))): @pgrm_trace * ((input * mem) * (output * mem))): Prop :=
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

    (* converts a postcondition for instant n into a precondition for instant n+1  *)
    Definition postcond_to_precond (post: local_postcond) : local_precond := fun t => match t with
    | nil => fun _ => True (* no history *)
    | prev_inst::h =>  fun _ => 
        post h (fst (fst prev_inst), snd (fst prev_inst)) (fst (snd prev_inst), snd (snd prev_inst))
    end.

    (* disjunction of all predecesssors postcondition as precondition *)
    Inductive join_preds (a: automaton ag_aut_node ag_aut_label) tr i m : ag_aut_node -> Prop :=
    | join_preds_setup :
        tr = nil /\ contract_setup C m ->
        join_preds a tr i m (init a) 

    | join_preds_cons prev_n precond curr_n : 
        predecessor _ _ a prev_n precond curr_n -> 
        postcond_to_precond (snd precond) tr (i,m) ->
        join_preds a tr i m curr_n
    .  


    Inductive triple_gen (a: automaton ag_aut_node ag_aut_label) (t: HoareTriple) n pre post tr i m o m' : Prop := 
    | triple_gen__cons :
        (* the triple precondition must be equivalent to the conjunction of the disjunction of previous postconditions and current precondition *)
        (local_pre t tr (i,m) <-> (join_preds a tr i m n /\ pre (private_to_input_trace tr) i)) -> 
        (local_post t tr (i,m) (o,m') <-> post tr (i,m) (o,m'))  ->
        body t = loop P ->
        triple_gen a t n pre post tr i m o m'
    .


    Definition valid_generated_triples   : Prop := 
        forall n , 
        reachable ag_aut n ->
        forall pre post next_node , 
        successor _ _ ag_aut next_node (pre,post) n  ->
        forall tr i m o m',
        exists t, triple_gen ag_aut t n pre post tr i m o m' /\ valid_triple t tr i m o m'
    .

End Reduction.


Abbreviation ag_aut_node := (a_aut_node * g_aut_node)%type.
Abbreviation ag_aut_label  := (a_aut_label * g_aut_label)%type.

Definition valid_contract_wit (C: Contract) (P: Program): Prop := 
    (contract_setup C) (setup P tt) ->
    forall t, 
    run P t ->
    forall i_tr m_tr o_tr m'_tr,
    ((i_tr,m_tr),(o_tr,m'_tr)) = pgrm_trace_split t ->
    forall a_p, language_wit sat_a (contract_assumes C) a_p (build_trace_history i_tr) -> 
    exists ag_p, 
        left_proj ag_p = a_p /\
        language_wit sat_ag (ag_aut C) ag_p (build_trace_history t)
.

Lemma valid_contract_wit_valid C P : valid_contract_wit C P -> valid_contract C P.
Proof.
    intros  Hvalid_wit Hvalid_setup t Hrun i_tr m_tr [o_tr m'_tr] Hsplit Ha_lang.
    destruct Ha_lang as (a_path & Ha_path & Ha_path_valid).
    specialize (Hvalid_wit Hvalid_setup t Hrun i_tr m_tr o_tr m'_tr Hsplit a_path (conj Ha_path Ha_path_valid))
         as (ag_path & Hag_p_a & Hag_path & Hag_path_valid).
    exists (right_proj ag_path); split.
    - now apply path_right_proj in Hag_path.
    - eapply valid_right_proj  with  (sat:= sat_g) (transf:=id) in Hag_path_valid.
        + replace (map fst (right_proj ag_path)) with (map snd (map fst ag_path)).
            ++ now rewrite map_id in Hag_path_valid.
            ++ clear. induction ag_path; [reflexivity|simpl; f_equal; apply IHag_path].
        + intros * Hsat_ag. red in Hsat_ag. destruct b as [t'  ([i m] & [o m'])]. now apply Hsat_ag. 
Qed.



Theorem correctness_aux P C: 
    valid_generated_triples P C -> 
    valid_contract_wit C P. 
Proof.
    intros Htriples Hvalid_setup tr Hrun. induction Hrun.

    - (* first instant  *) 
        intros i_tr m_tr o_tr m'_tr Htr_split a_path Ha_lang.
        inversion Htr_split; subst.
        rewrite build_trace_history_cons in Ha_lang |- *.


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

                               
            assert (Hinitreach : reachable (ag_aut C) (init (a_aut C), init (g_aut C))) by now constructor.
            destruct (Htriples _ Hinitreach a_curr_label g_curr_label (a_next_node,g_next_node) Hag_trans nil i (setup P tt) o m')
                 as (t & Htriples_gen & Htriples_valid).
            inversion_clear Htriples_gen as  [Ht_pre Ht_post Ht_body].

            (* this gives us the postcondition *)
            rewrite <- Ht_post; apply Htriples_valid; [|now rewrite Ht_body]. 
            rewrite Ht_pre;  cbn; split; [|assumption]. now constructor.
        }

        exists (((a_curr_label,g_curr_label), (a_next_node,g_next_node))::nil). split; [reflexivity|].

        split.
        *  exact (path_transition _ _ _ _ _ _ ag_aut_trans).
        *  assert (Hag_sat : sat_ag (a_curr_label, g_curr_label) (nil, ((i,setup P tt,(o, m')))))
                by easy.
            exact (valid_cons _ _ _ _ _ _ _ (valid_nil _ _ _) Hag_sat).


    -  (* nth instant *)
        intros i_tr m_tr o_tr m'_tr Htr_split a_path Ha_lang. 
        apply (pgrm_trace_split_inv ( (prev_i, prev_m, (prev_o, m)) :: tr) i m o m' i_tr m_tr o_tr m'_tr) in Htr_split 
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


        apply (pgrm_trace_split_inv tr prev_i prev_m prev_o m i_tr m_tr o_tr) in Htr_split as 
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

        assert (Hag_succ: successor _ _ (ag_aut C) (a_next_node, g_next_node) (a_curr_label, g_curr_label) (a_curr_node, g_curr_node)) by easy. 


        specialize (Htriples  (a_curr_node, g_curr_node) Hag_curr_reach a_curr_label g_curr_label (a_next_node,g_next_node) Hag_succ ((prev_i, prev_m, (prev_o, m)) :: tr) i m o m') 
            as (t & Htriple_gen & Hvalid_triple);
        destruct Htriple_gen as [Hcurr_t_pre Hcurr_t_post Hcurr_t_body].

        exists (((a_curr_label,g_curr_label), (a_next_node,g_next_node))::((a_prev_label,g_prev_label), (a_curr_node,g_curr_node))::ag_path).
        split; [reflexivity|]; split; cbn.

        + now constructor.
        + constructor; [now constructor|]; split; cbn.
            * unfold private_to_input_trace; rewrite pgrm_trace_split_cons; cbn; subst.
                now  inversion_clear Htr_split; cbn.
                
            *  rewrite <- Hcurr_t_post.
                apply Hvalid_triple; [|now rewrite Hcurr_t_body ]; clear Hcurr_t_body.
                rewrite Hcurr_t_pre. split.
                -- inversion Hag_path as [X|? ? Hprev_trans X |ag_prev_node ? ag_prev_label ? ag_path' Hprev_path Hprev_trans X]; subst.
                    ++ now constructor 2 with (precond:=(a_prev_label, g_prev_label)) (prev_n:=(init (ag_aut C))).
                    ++ now constructor 2 with (precond:=(a_prev_label, g_prev_label)) (prev_n:=(ag_prev_node)).                    
                -- unfold private_to_input_trace; rewrite pgrm_trace_split_cons; cbn; subst.
                    now inversion_clear Htr_split; cbn.
Qed.


Corollary correctness P C : 
    valid_generated_triples P C -> 
    valid_contract C P. 
Proof.
    intros Hvalid; apply valid_contract_wit_valid; apply correctness_aux; assumption.
Qed.
