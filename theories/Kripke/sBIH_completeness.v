Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Syntax.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import BiInt_extens_interactions.
Require Import wBIH_meta_interactions.
Require Import sBIH_meta_interactions.
Require Import BiInt_Kripke_sem.
Require Import BiInt_bisimulation.
Require Import BiInt_Lindenbaum_lem.
Require Import wBIH_completeness.

Axiom LEM : forall P, P \/ ~ P.

Lemma DN_form_DN : forall n A, (DN_form (S n) A) = (DN_form n (¬ (∞ A))).
Proof.
induction n.
- intros. simpl. auto.
- intros. simpl. pose (IHn A). rewrite <- e. simpl. auto.
Qed.

Lemma DN_clos_DN_form : forall n Γ A, (In _ Γ A) -> (In _ (DN_clos_set Γ) (DN_form n A)).
Proof.
induction n.
- intros. simpl. apply InitClo. auto.
- intros. simpl. apply IndClo. apply IHn. auto.
Qed.

Section pruning.

(* We define how to prune a model M in a point s. *)

Variable M : model.
Variable s : (@nodes M).

Fixpoint n_reachable (n: nat) (w v : @nodes M) : Prop :=
  match n with
  | 0 => w = v
  | S m => (exists u, (((@reachable M) u v) \/ ((@reachable M) v u)) /\ (n_reachable m w u))
  end.

Lemma n_reachable_DN_clos : forall n w A,
  (wforces M w (DN_form n A)) ->
    (forall v, (n_reachable n w v) -> (wforces M v A)).
Proof.
induction n.
- intros. simpl in H. inversion H0. subst. auto.
- intros. inversion H0. destruct H1. destruct H1.
  * pose (IHn w (¬ (∞ A))). pose (DN_form_DN n A). rewrite e in H.
    pose (w0 H x H2). simpl in w1. pose (w1 v H1).
    destruct (LEM (wforces M v A)) ; auto. exfalso.
    pose (w0 H). pose (w1 _ H1).
    assert ((exists v0 : nodes, reachable v0 v /\ (wforces M v0 A -> False))).
    exists x. repeat split ; auto. intros. apply H3.
    apply Persistence with (w:=x) ; auto. destruct H4. destruct H4. apply f0 ; auto.
  * pose (IHn w (¬ (∞ A))). pose (DN_form_DN n A). rewrite e in H.
    pose (w0 H x H2). simpl in w1. pose (w1 x).
    destruct (LEM (wforces M v A)) ; auto. exfalso.
    assert (exists v : nodes, reachable v x /\ (wforces M v A -> False)).
    exists v. repeat split ; auto. destruct H4. destruct H4.
    apply f. apply (@reach_refl M). intro. apply H5 ; auto.
Qed.

Definition s_is_n_reachable (w : @ nodes M) : Prop :=
  exists n, @n_reachable n s w.

Definition s_pruned_worlds : Type :=
  { x  | s_is_n_reachable x}.

Definition s_pruned_rel (pw0 pw1 : s_pruned_worlds) : Prop :=
  (@reachable M) (proj1_sig pw0) (proj1_sig pw1).

Definition s_pruned_val (pw : s_pruned_worlds) (q : nat) : Prop :=
  val (proj1_sig pw) q.

Lemma s_R_refl u :  (s_pruned_rel) u u.
Proof.
intros. unfold s_pruned_rel. destruct u.
simpl. auto. apply (@reach_refl M).
Qed.

Lemma s_R_trans u v w: (s_pruned_rel u v) -> (s_pruned_rel v w) -> (s_pruned_rel u w).
Proof.
intros. unfold s_pruned_rel. destruct w. destruct u. simpl.
unfold s_pruned_rel in H. simpl in H. unfold s_pruned_rel in H0. simpl in H0.
destruct v. simpl in H. simpl in H0. apply ((@reach_tran M) _ _ _ H H0).
Qed.

Lemma s_val_persist : forall u v, s_pruned_rel u v -> forall p, (s_pruned_val u p -> s_pruned_val v p).
Proof.
intros.
unfold s_pruned_val in H0. unfold s_pruned_rel in H.
unfold s_pruned_val. destruct u. destruct v. simpl. simpl in H0.
simpl in H. apply ((@persist M) _ _ H). auto.
Qed.

Instance pruned_M : model :=
      {|
        nodes := s_pruned_worlds ;
        reachable := s_pruned_rel ;
        val := s_pruned_val ;

        reach_refl := s_R_refl ;
        reach_tran := s_R_trans ;

        persist := s_val_persist ;
      |}.

Lemma pruned_bisim : bisimulation M pruned_M
(fun (x : (@nodes M)) (y : (@nodes pruned_M)) => x = (proj1_sig y)).
Proof.
intros. unfold bisimulation. intros. subst. repeat split ; intros ; auto.
- exists (proj1_sig v1). split ; auto.
- destruct w1. simpl in H.
  assert (J20: s_is_n_reachable v0).
  unfold s_is_n_reachable. unfold s_is_n_reachable in s0.
  destruct s0. exists (S x0). simpl. exists x. split ; auto.
  pose(@exist  (@nodes M) s_is_n_reachable v0 J20). exists s1.
  auto.
- destruct w1. simpl in H. simpl. destruct v1. simpl.
  simpl in H. exists x0. split ; auto.
- destruct w1. simpl. simpl in H.
  assert (J20: s_is_n_reachable v0).
  unfold s_is_n_reachable. unfold s_is_n_reachable in s0.
  destruct s0. exists (S x0). simpl. exists x. split ; auto.
  pose(@exist  (@nodes M) s_is_n_reachable v0 J20). exists s1.
  auto.
Qed.

Lemma pruned_wforces : forall (pw : (@nodes pruned_M)) A,
  (wforces pruned_M pw A) <-> (wforces M (proj1_sig pw) A).
Proof.
intros.
pose (bisimulation_imp_bi_int_equiv M pruned_M
(fun (x : (@nodes M)) (y : (@nodes pruned_M)) => x = (proj1_sig y))
pruned_bisim A (proj1_sig pw) pw). split ; apply i ; auto.
Qed.

End pruning.

Theorem sQuasiCompleteness : forall Γ A,
    ~ sBIH_prv Γ A ->  ~ glob_conseq Γ A.
Proof.
intros Γ A SD.
assert (J1: sBIH_prv (DN_clos_set Γ) A -> False).
{ intro. apply SD. apply (sBIH_comp _ _ H). intros.
  induction H0.
  - apply sId ; auto.
  - apply sDN ; auto. }
assert (J2: wBIH_prv (DN_clos_set Γ) A -> False).
intro. apply J1. apply sBIH_extens_wBIH ; auto.
pose (wQuasiCompleteness _ _ J2).
intro. apply n. intros M w Hw. pose (pruned_bisim M w).

(* All formulae in Γ are globally true in the pruned canonical model. *)
assert (SAT: forall (pw : (s_pruned_worlds M w)) C, (In _ Γ C) ->
wforces (pruned_M M w) pw C).
{ intros. pose (bisimulation_imp_bi_int_equiv M (pruned_M M w) _ b).
  pose (i C (proj1_sig pw) pw). apply i0. auto. clear i0. clear i. destruct pw. simpl.
  unfold s_is_n_reachable in s. destruct s.
  assert (J5: wforces M w (DN_form x0 C)).
  { apply Hw. apply DN_clos_DN_form ; auto. }
  pose (n_reachable_DN_clos M x0 w C J5 x). auto. }

assert (J20: s_is_n_reachable M w w). unfold s_is_n_reachable. exists 0.
unfold n_reachable. auto.
pose (@exist (@nodes M) (s_is_n_reachable M w) w J20).
assert (wforces (pruned_M M w) s A).
apply H. intros. intro. apply SAT ; auto.
pose (bisimulation_imp_bi_int_equiv _ _ _ b A w s).
apply i ; auto.
Qed.

Theorem sCompleteness : forall Γ A,
    glob_conseq Γ A -> sBIH_prv Γ A.
Proof.
intros Γ A GC. pose (sQuasiCompleteness Γ A).
pose (LEM (sBIH_prv Γ A)). destruct o. auto. exfalso.
apply n ; assumption.
Qed.