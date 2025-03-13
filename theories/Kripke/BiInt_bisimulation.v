Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import Syntax.
Require Import BiInt_GHC.
Require Import BiInt_Kripke_sem.

Section Bisimulation.

(* Define the notion of bisimulation. *)

Definition bisimulation (M0 M1 : model) (B : (@nodes M0) -> (@nodes M1) -> Prop) : Prop :=
  forall (w0 : @nodes M0) (w1 : @nodes M1), (B w0 w1) ->
 (* B1 *) ((forall p, (@val M0) w0 p <-> (@val M1) w1 p) /\
 (* B2 *) (forall v1, ((@reachable M1) w1 v1) -> (exists v0, ((@reachable M0) w0 v0) /\ (B v0 v1))) /\
 (* B3 *) (forall v0, ((@reachable M0) w0 v0) -> (exists v1, ((@reachable M1) w1 v1) /\ (B v0 v1)))) /\
 (* B4 *) (forall v1, ((@reachable M1) v1 w1) -> (exists v0, ((@reachable M0) v0 w0) /\ (B v0 v1))) /\
 (* B5 *) (forall v0, ((@reachable M0) v0 w0) -> (exists v1, ((@reachable M1) v1 w1) /\ (B v0 v1))).

(* Show that bisimulation implies bi-intuitionistic equivalence. *)

Lemma bisimulation_imp_bi_int_equiv : forall (M0 M1 : model) (B :(@nodes M0) -> (@nodes M1) -> Prop),
  (bisimulation M0 M1 B) ->
  (forall A w0 w1, (B w0 w1) ->
    ((wforces M0 w0 A) <-> (wforces M1 w1 A))).
Proof.
intros M0 M1 B H.
induction A ; split ; intro.
  * simpl. simpl in H1. unfold bisimulation in H. pose (H w0 w1 H0).
    destruct a. apply H2. auto.
  * simpl. simpl in H1. unfold bisimulation in H. pose (H w0 w1 H0).
    destruct a. apply H2. auto.
  * simpl. inversion H1.
  * simpl. inversion H1.
  * simpl in H1. apply I.
  * apply I.
  * simpl in H1. destruct H1. simpl. split. pose (IHA1 w0 w1 H0). apply i. auto.
    pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. destruct H1. simpl. split. pose (IHA1 w0 w1 H0). apply i. auto.
    pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. simpl. destruct H1. left. pose (IHA1 w0 w1 H0). apply i. auto.
    right. pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. simpl. destruct H1. left. pose (IHA1 w0 w1 H0). apply i. auto.
    right. pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl. simpl in H1. intros. unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H5. destruct H4. clear H4. destruct H5. clear H5.
    pose (H4 _ H2). destruct e. destruct H5.
    pose (IHA1 x v H6). apply i in H3. apply H1 in H3. 2: auto.
    pose (IHA2 x v H6). apply i0. auto.
  * simpl. simpl in H1. intros. unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H5. destruct H4. clear H4.
    destruct H5. clear H4.
    pose (H5 _ H2). destruct e. destruct H4.
    pose (IHA1 v x H6). apply i in H3. apply H1 in H3. 2: auto.
    pose (IHA2 v x H6). apply i0. auto.
  * simpl. simpl in H1. intro. apply H1. intros. unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H5. destruct H6. clear H5.
    pose (H6 _ H3). destruct e. destruct H5. 
    pose (IHA1 v x H7). apply i in H4.
    pose (IHA2 v x H7). apply i0. auto.
  * simpl. simpl in H1. intro. apply H1. intros. 
    unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H5. destruct H6. clear H6.
    pose (H5 _ H3). destruct e. destruct H6.
    pose (IHA1 x v H7). apply i in H4.
    pose (IHA2 x v H7). apply i0. auto.
Qed.

End Bisimulation.

Section n_Bisimulation.

Fixpoint n_bisimulation (n : nat) (M0 M1 : model) (w0 : @nodes M0) (w1 : @nodes M1) : Prop :=
match n with
| 0 => (forall p, (@val M0) w0 p <-> (@val M1) w1 p)
| S k =>  
 (* nB1 *) (forall p, (@val M0) w0 p <-> (@val M1) w1 p) /\
 (* nB2 *) (forall v1, ((@reachable M1) w1 v1) -> (exists v0, ((@reachable M0) w0 v0) /\ (n_bisimulation k M0 M1 v0 v1))) /\
 (* nB3 *) (forall v0, ((@reachable M0) w0 v0) -> (exists v1, ((@reachable M1) w1 v1) /\ (n_bisimulation k M0 M1 v0 v1))) /\
 (* nB4 *) (forall v1, ((@reachable M1) v1 w1) -> (exists v0, ((@reachable M0) v0 w0) /\ (n_bisimulation k M0 M1 v0 v1))) /\
 (* nB5 *) (forall v0, ((@reachable M0) v0 w0) -> (exists v1, ((@reachable M1) v1 w1) /\ (n_bisimulation k M0 M1 v0 v1)))
end.

Lemma n_bisimulation_S (n : nat) (M0 M1 : model) (w0 : @nodes M0) (w1 : @nodes M1) :
  n_bisimulation (S n) M0 M1 w0 w1 -> n_bisimulation n M0 M1 w0 w1.
Proof.
revert n M0 M1 w0 w1.
induction n ; intros.
- inversion H ; subst ; auto.
- cbn. destruct H as (B1 & B2 & B3 & B4 & B5). split ; auto.
  repeat split ; auto.
  + intros. destruct (B2 _ H) as (u & Hu0 & Hu1). exists u ; split ; auto.
  + intros. destruct (B3 _ H) as (u & Hu0 & Hu1). exists u ; split ; auto.
  + intros. destruct (B4 _ H) as (u & Hu0 & Hu1). exists u ; split ; auto.
  + intros. destruct (B5 _ H) as (u & Hu0 & Hu1). exists u ; split ; auto.
Qed.

Lemma n_bisimulation_cum (n m : nat) (M0 M1 : model) (w0 : @nodes M0) (w1 : @nodes M1) :
  m <= n -> n_bisimulation n M0 M1 w0 w1 -> n_bisimulation m M0 M1 w0 w1.
Proof.
revert n m M0 M1 w0 w1.
apply (well_founded_induction_type lt_wf (fun n => 
forall (m : nat) (M0 M1 : model) (w0 w1 : nodes),
m <= n -> n_bisimulation n M0 M1 w0 w1 -> n_bisimulation m M0 M1 w0 w1)).
intros n IHn m M0 M1 w0 w1 H H0.
destruct n. 
- inversion H ; subst ; auto.
- inversion H ; subst ; auto.
  apply IHn with n ; try lia ; auto. apply n_bisimulation_S ; auto.
Qed.

Lemma n_bisimulation_imp_n_depth_equiv : forall n (M0 M1 : model) (w0 : @nodes M0) (w1 : @nodes M1),
  (n_bisimulation n M0 M1 w0 w1) ->
  (forall ϕ, depth ϕ <= n ->
    ((wforces M0 w0 ϕ) <-> (wforces M1 w1 ϕ))).
Proof.
induction n.
- intros. exfalso ; apply (depth_zero ϕ) ; lia.
- intros M0 M1 w0 w1 Hbisim ϕ. revert M0 M1 w0 w1 Hbisim. 
  induction ϕ ; intros M0 M1 w0 w1 Hbisim ; cbn ; auto.
  + firstorder.
  + firstorder.
  + firstorder.
  + intro H. split ; intro H5.
    * destruct H5. split. 
      -- apply IHϕ1 with (w0:=w0) ; auto ; lia.
      -- apply IHϕ2 with (w0:=w0) ; auto ; lia.
    * destruct H5. split. 
      -- apply IHϕ1 with (w1:=w1) ; auto ; lia.
      -- apply IHϕ2 with (w1:=w1) ; auto ; lia.
  + intro H. split ; intro H5.
    * destruct H5.
      -- left ; apply IHϕ1 with (w0:=w0) ; auto ; lia.
      -- right ; apply IHϕ2 with (w0:=w0) ; auto ; lia.
    * destruct H5.
      -- left ; apply IHϕ1 with (w1:=w1) ; auto ; lia.
      -- right ; apply IHϕ2 with (w1:=w1) ; auto ; lia.
  + intro H. split ; intro H5.
    * intros v1 w1Rv1 Hv1. inversion Hbisim as (H0 & H1 & H2 & H3 & H4).
      apply H1 in w1Rv1. destruct w1Rv1 as (v0 & w0Rv0 & Hv0).
      apply IHn with (w0:=v0) ; auto ; try lia. apply H5 ; auto.
      apply IHn with (w1:=v1) ; auto ; try lia.
    * intros v0 w0Rv0 Hv0. inversion Hbisim as (H0 & H1 & H2 & H3 & H4).
      apply H2 in w0Rv0. destruct w0Rv0 as (v1 & w1Rv1 & Hv1).
      apply IHn with (w1:=v1) ; auto ; try lia. apply H5 ; auto.
      apply IHn with (w0:=v0) ; auto ; try lia.
  + intro H. split ; intros H5 H6.
    * apply H5. intros v0 v0Rw0 Hv0. inversion Hbisim as (H0 & H1 & H2 & H3 & H4).
      apply H4 in v0Rw0. destruct v0Rw0 as (v1 & v1Rw1 & Hv1).
      apply IHn with (w1:=v1) ; auto ; try lia. apply H6 ; auto.
      apply IHn with (w0:=v0) ; auto ; try lia.
    * apply H5. intros v1 v1Rw1 Hv1. inversion Hbisim as (H0 & H1 & H2 & H3 & H4).
      apply H3 in v1Rw1. destruct v1Rw1 as (v0 & w0Rv0 & Hv0).
      apply IHn with (w0:=v0) ; auto ; try lia. apply H6 ; auto.
      apply IHn with (w1:=v1) ; auto ; try lia.
Qed.

End n_Bisimulation.





