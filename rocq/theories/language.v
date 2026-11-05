From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From MMaps Require Import MMaps.
From Stdlib Require Import Structures.OrdersEx.
From Hardy Require Import verification.



Definition Id : Type := nat.
Inductive Ty := Ty_int | Ty_bool.
Inductive Value := VInt : Z -> Value | VBool : bool -> Value.

Module IdMap := OrdList.Make(Nat_as_OT).

Module Import T <: TraceType.
    Definition input :=  IdMap.t Value.
    Definition output :=  IdMap.t Value.
    Definition state :=  IdMap.t Value.
End T.

Module Trace := Trace(T).
Module Contract := Contract(T).
Import Trace Contract.

Definition ty_of_value (v:Value) : Ty := match v with VInt _ => Ty_int | VBool _ => Ty_bool end.

Definition params : Type := list (Id * Ty).

Definition wt_args (args: list Value) (p:params) : Prop := List.Forall2 (fun a p => ty_of_value a = snd p) args p.



Scheme All for list.

Inductive IntBinOp := Plus | Minus | Mult | Div.
Inductive BoolBinOp := And | Or.
Inductive BoolUnOp := Not.
Inductive IntUnOp := Opp.


Definition IntBinOpToZ (op:IntBinOp) : Z -> Z -> Z := match op with
    | Plus => Z.add
    | Minus => Z.sub
    | Mult => Z.mul
    | Div => Z.div
end.

Definition IntUnopToZ (op: IntUnOp) : Z -> Z := match op with Opp => Z.opp end.

(* Definition BoolUnopToBool (op: BoolBinOp) : bool -> bool -> bool := match op with And => andb | Or => orb end.

Definition BoolBinOptoBool (op: BoolUnOp) : bool -> bool := match op with Neg => negb end. *)

Inductive Expression :=
    | E_Var (x:Id)
    | E_Const : Value -> Expression
    | E_BinArith : Expression -> IntBinOp -> Expression -> Expression 
.

Inductive _Statement (Ext : Type) := 
    | S_Assign (v:Id) (e:Expression)
    | S_Condition (cond:Expression) (yes:_Statement Ext) (no:_Statement Ext)
    | S_Sequence (s1 : _Statement Ext) (s2: _Statement Ext)
    | S_Ext (ext:Ext)
.

Definition Statement := _Statement False.

Inductive Reactive := 
    | R_Emit (v:Id) (e:Expression)
    | R_NodeCall (v:Id) (args: list Expression)
.

Definition RStatement := _Statement Reactive.


Record Node := {
    node_name: Id ;

    node_params :  list (Id * Ty) ;
    node_inputs : list (Id * Ty) ;
    node_outputs :  list (Id * Ty) ;

    node_instances : Id -> Prop ;

    (* right element represents instances initialization*)
    node_setup : Statement * ((Id * list Expression) -> Prop) ; 
    
    node_loop : RStatement ;
}.

Record NodeContract :=  {
    LoopInvariant : instant -> Prop;
    TemporalContract : Contract
}.
Record Program : Type :=  {
    pgrm_start : Id;
    pgrm_args : list Value;
    pgrm_nodes : (Node * NodeContract) -> Prop;
}.

(* Record WTP (P : program) := {
    (* the start node exists *)
    Hstart : exists C, In _ P.(Nodes) C /\ C.(Name) = P.(Start) ;
    
    (* all declared instances of each declared node exist *)
    Hinst : forall C, In _ P.(Nodes) C -> 
                forall Sub, In _ C.(Instances) Sub -> 
                    exists C', In _ P.(Nodes) C' /\ C'.(Name) = Sub ;
}. *)

Record Environnement := {
    env_node_decls : (Node * NodeContract) -> Prop;
    env_node_args : list Value;
    env_node_inputs : list Value;
}.



(* Inductive node_start (N: Node) : pgrm_trace -> Prop :=
| NodeStart t : 
    forall i params, In _ (snd N.(Setup)) (i,params) ->
    In _ (snd N.(Setup)) (i,params) ->
    True
. *)

(* Inductive program_eval (P: program) : pgrm_trace -> Prop := 
| PEval N t : 
    N.(Name) = P.(Start) -> 
    In _ P.(Nodes) N ->
    node_eval N t -> 
    program_eval P t. *)
Inductive eval_expr (st: state) : Expression -> Value -> Prop :=
| eval_e_bool b : eval_expr st (E_Const (VBool b)) (VBool b)
| eval_e_int z : eval_expr st (E_Const (VInt z)) (VInt z)
| eval_e_var x v : 
    IdMap.find x st = Some v -> 
    eval_expr st (E_Var x) v
| eval_e_binarith e1 v1 e2 v2 op : 
    eval_expr st e1 (VInt v1) ->
    eval_expr st e2 (VInt v2) ->
    eval_expr st (E_BinArith e1 op e2) (VInt (IntBinOpToZ op v1 v2))
.


Inductive eval_stmt (env: Environnement) (st: state)  : Statement -> state -> Prop :=
    | eval_s_assign x e v: 
        eval_expr st e v ->
        IdMap.mem x st = true -> 
        eval_stmt env st (S_Assign _ x e) (IdMap.add x v st)
    
    | eval_s_cond_true cond y n st' : 
        eval_expr st cond  (VBool true) ->
        eval_stmt env st y st' ->
        eval_stmt env st (S_Condition _ cond y n) st'

    | eval_s_cond_false cond y n st' : 
        eval_expr st cond  (VBool false) ->
        eval_stmt env st n st' ->
        eval_stmt env st (S_Condition _ cond y n) st'

    | eval_s_statement s1 s2 st' st'' :
        eval_stmt env st s1 st' ->
        eval_stmt env st' s2 st'' ->
        eval_stmt env st (S_Sequence _ s1 s2) st''
.



Definition wt_instances (P: Program ): Prop := forall C, P.(pgrm_nodes) C -> 
                forall Sub,  (fst C).(node_instances) Sub -> 
                    exists C', P.(pgrm_nodes) C' /\ (fst C').(node_name) = Sub.


Scheme All for prod.

Inductive Ω := {
    state : state ;
    instances : list (Node * Ω) ;
}.

(* Inductive node_setup : :=  *)


(* Inductive node_eval (N: Node) (ω: Ω) : pgrm_trace -> Prop :=
    | NodeStart st st': 
        (* instances setup *)
        forall n'_name n'_params, 
        (snd N.(node_setup)) (n'_name,n'_params) ->
        (* no recursive instance *)
        n'_name <> N.(node_name) ->

        (* find the node declaration with the given name *)
        forall N' c, 
        E.(env_node_decls) (N',c) ->
        N'.(node_name) = n'_name -> True
        
        eval_stmt st (fst N.(node_setup))  st' ->
        
        node_eval N E nil

    | NodeNext : 
        wt_args E.(env_node_inputs) N.(node_inputs) ->
        node_eval N E nil 
. *)

(* 
Inductive program_eval (P: Program) : pgrm_trace -> Prop := 
| PEval N C t : 
    N.(node_name) = P.(pgrm_start) -> 
    Ensembles.In _ P.(pgrm_nodes) (N,C) ->
    wt_args P.(pgrm_args) N.(node_params) ->
    node_eval N {|env_node_decls := P.(pgrm_nodes); env_node_args := P.(pgrm_args) ; env_node_inputs := nil|} t -> 
    program_eval P t
. *)

