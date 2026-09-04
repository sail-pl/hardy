From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Ensembles.
From Hardy Require Import verification.


Definition id : Type := string.
Inductive Ty := Ty_int | Ty_bool.
Inductive Value := VInt : Z -> Value | VBool : bool -> Value.

Definition params : Type := list (id * Ty).


Scheme All for list.

Inductive Expression :=
    | Var (v:id)
    | BoolConst : bool -> Expression
    | IntConst : Z -> Expression
    | InstCall (name: id) (inputs_binders: list Expression)
.

Inductive Statement := 
    | Assign (v:id) (e:Expression)
    | Condition (cond:Expression) (yes:Statement) (no:Statement)
    | Sequence (s1 : Statement) (s2: Statement)
.

Definition State := Ensemble (id * Value).


Record Node := {
    Name: id ;

    Params :  list (id * Ty) ;
    Inputs : list (id * Ty) ;
    Outputs :  list (id * Ty) ;

    Instances : Ensemble id ;

    (* right element represents instances initialization*)
    Setup : Statement *  Ensemble (id * list Expression) ; 
    
    Loop : Statement ;
}.

Record NodeContract :=  {
    LoopInvariant : instant -> Prop;
    TemporalContract : Contract
}.


Record program : Type :=  {
    Start : id;
    Nodes : Ensemble Node;
}.

Record WTP (P : program) := {
    (* the start node exists *)
    Hstart : exists C, In _ P.(Nodes) C /\ C.(Name) = P.(Start) ;
    
    (* all declared instances of each declared node exist *)
    Hinst : forall C, In _ P.(Nodes) C -> 
                forall Sub, In _ C.(Instances) Sub -> 
                    exists C', In _ P.(Nodes) C' /\ C'.(Name) = Sub ;
}.

Record WTN (N: Node) := {
    (* the current node cannot declare an instance of itself *)
    Hnonrec_inst : 
}

Inductive Environnement := {

}.


Inductive node_start (N: Node) (): pgrm_trace -> Prop :=
| NodeStart t : 
    forall i params, In _ (snd N.(Setup)) (i,params) ->
    In _ (snd N.(Setup)) (i,params) ->

.

Inductive program_eval (P: program) : pgrm_trace -> Prop := 
| PEval N t : 
    N.(Name) = P.(Start) -> 
    In _ P.(Nodes) N ->
    node_eval N t -> 
    program_eval P t.

