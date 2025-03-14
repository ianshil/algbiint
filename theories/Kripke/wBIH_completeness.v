Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Syntax.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import wBIH_meta_interactions.
Require Import BiInt_Kripke_sem.
Require Import BiInt_Lindenbaum_lem.
Require Import BiInt_soundness.

Section LEM_completeness.

Class Canon_worlds : Type :=
  { prim : @Ensemble form ;
    NotDer : ~ (wBIH_prv prim Bot) ;
    Closed : closed prim ;
    Stable : stable prim ;
    Prime : prime prim
  }.

Definition Canon_rel (P0 P1 : Canon_worlds) : Prop :=
  Included _ (@prim P0) (@prim P1).

Definition Canon_val (P : Canon_worlds) (q : nat) : Prop :=
  In _ prim (# q).

Lemma C_R_refl u : Canon_rel u u.
Proof.
unfold Canon_rel. intro. auto.
Qed.

Lemma C_R_trans u v w: Canon_rel u v -> Canon_rel v w -> Canon_rel u w.
Proof.
intros. intro. intros. auto.
Qed.

Lemma C_val_persist : forall u v, Canon_rel u v -> forall p, Canon_val u p -> Canon_val v p.
Proof.
intros. apply H. auto.
Qed.

Instance CM : model :=
      {|
        nodes := Canon_worlds ;
        reachable := Canon_rel ;
        val := Canon_val ;

        reach_refl := C_R_refl ;
        reach_tran := C_R_trans ;

        persist := C_val_persist ;
      |}.

Axiom LEM : forall P, P \/ ~ P.

Lemma LEM_prime Γ :
  quasi_prime Γ -> prime Γ.
Proof.
  intros H1 A B H2.
  apply H1 in H2. destruct (LEM (Γ A)) ; auto.
  destruct (LEM (Γ B)) ; auto. exfalso. apply H2.
  intro. destruct H3 ; auto.
Qed.

Lemma LEM_Lindenbaum Γ Δ :
  ~ wpair_der Γ Δ ->
  exists Γm, Included _ Γ  Γm
           /\ closed Γm
           /\ prime Γm
           /\ ~ wpair_der Γm Δ.
Proof.
intros.
exists (prime_theory Γ Δ).
repeat split.
- intro. apply prime_theory_extens.
- apply closeder_fst_Lind_pair ; auto.
- apply LEM_prime. apply quasi_prime_Lind_pair ; auto.
- intro. apply Under_Lind_pair_init in H0 ; auto.
Qed.

Lemma LEM_world Γ Δ :
  ~ wpair_der Γ Δ ->
  exists w : Canon_worlds, Included _ Γ prim /\ Included _ Δ (Complement _ prim).
Proof.
  intros (Γm & Γn & H1 & H2 & H3) % LEM_Lindenbaum.
  unshelve eexists.
  - apply (Build_Canon_worlds Γm); intuition ; simpl.
    apply H3. exists [] ; repeat split ; auto. apply NoDup_nil.
    intros ; auto. inversion H0. intros A H5.
    destruct (LEM (Γm A)) ; intuition.
  - intuition. intros A HA0 HA1. apply H3. exists [A].
    simpl ; repeat split ; auto. apply NoDup_cons. intro H8 ; inversion H8.
    apply NoDup_nil. intros. destruct H ; try contradiction. subst ; auto.
    unfold In in HA1. unfold prim in HA1.
    eapply wMP. apply wAx ; eapply A3 ; reflexivity.
    apply wId ; auto.
Qed.

Lemma truth_lemma : forall A (cp : Canon_worlds),
  (wforces CM cp A) <-> (In _ (@prim cp) A).
Proof.
induction A ; intro ; split ; intros ; simpl ; try simpl in H ; auto.
(* Bot *)
- inversion H.
- apply NotDer. apply wId ; auto.
(* Top *)
- apply Closed. apply prv_Top.
(* And A1 A2 *)
- destruct H. apply IHA1 in H. simpl in H. apply IHA2 in H0. simpl in H0.
  apply Closed.
  eapply wMP. eapply wMP. eapply wMP.
  apply wAx ; eapply A8 ; reflexivity.
  apply imp_Id_gen.
  eapply wMP. apply Thm_irrel.
  all: apply wId ; auto.
- split. apply IHA1. apply Closed ; auto.
  eapply wMP. apply wAx ; eapply A6 ; reflexivity.
  apply wId ; exact H.
  apply IHA2. apply Closed ; auto.
  eapply wMP. apply wAx ; eapply A7 ; reflexivity.
  apply wId ; exact H.
(* Or A1 A2 *)
- destruct H.
  apply IHA1 in H. simpl in H. apply Closed ; auto. eapply wMP.
  apply wAx ; eapply A3 ; reflexivity. apply wId ; auto.
  apply IHA2 in H. simpl in H. apply Closed ; auto. eapply wMP.
  apply wAx ; eapply A4 ; reflexivity. apply wId ; auto.
- apply Prime in H ; auto. destruct H. left. apply IHA1 ; auto.
  right. apply IHA2 ; auto.
(* Imp A1 A2 *)
- apply Stable. intros H0.
  assert (wpair_der (Union _ (prim) (Singleton _ A1)) (Singleton _ A2) -> False).
  intro. apply gen_wBIH_Deduction_Theorem in H1. apply H0.
  { apply Closed. destruct H1.
    destruct H1. destruct H2. destruct x. simpl in H3. simpl in H2.
    eapply wMP. apply EFQ. auto. destruct (H2 f) ; cbn ; auto. cbn in H3.
    destruct x ; cbn in *. apply absorp_Or1 in H3 ; auto.
    exfalso. destruct (H2 f) ; auto. inversion H1 ; subst. apply H6 ; cbn ; auto. }
  pose (LEM_world _ _ H1). destruct e as [w [Hw1 Hw2]].
  assert (J2: Canon_rel cp w). unfold Canon_rel. simpl.
  intro. intros. apply Hw1. apply Union_introl. auto. apply H in J2.
  apply IHA2 in J2. assert (In form (Complement _ prim) A2). apply Hw2.
  apply In_singleton. apply H2 ; auto.
  apply IHA1. simpl. apply Hw1. apply Union_intror. apply In_singleton.
- intros.
  apply IHA1 in H1. simpl in H1. unfold Canon_rel in H0. simpl in H0.
  apply H0 in H.
  apply IHA2. simpl.
  assert (wpair_der prim (Singleton _ A2)). exists [A2]. repeat split.
  apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H2. subst. apply In_singleton.
  inversion H3. simpl.
  eapply wMP. apply wAx ; eapply A3 ; reflexivity.
  eapply wMP. apply wId ; exact H. apply wId ; auto.
  apply Closed. destruct H2. destruct H2.
  destruct H3. destruct x. simpl in H4. eapply wMP. apply EFQ. auto.
  destruct (H3 f) ; cbn ; auto. cbn in *. destruct x ; cbn in *.
  apply absorp_Or1 in H4 ; auto. exfalso.
  destruct (H3 f) ; cbn ; auto. inversion H2 ; subst.
  apply H7 ; cbn ; auto.
(* Excl A1 A2 *)
- apply Stable. intros Hw. apply H. intros. apply IHA1 in H1.
  assert (In form (prim) (Or A2 (Excl A1 A2))). {
  apply Closed.
  eapply wMP. apply wAx ; eapply BA1 ; reflexivity. apply wId ; auto. }
  apply Prime in H2. destruct H2 ; auto. apply IHA2 ; auto. contradict Hw. apply H0, H2.
- assert (wpair_der (Singleton _ A1) (Union _ (Complement _ prim) (Singleton _ A2)) -> False).
  { intro. destruct H0. destruct H0. destruct H1.
    pose (remove_disj x A2 (Singleton form A1)).
    assert (wBIH_prv (Singleton form A1) (Or A2 (list_disj (remove eq_dec_form A2 x)))).
    { eapply wMP. exact w. auto. }
    assert (Singleton form A1 = Union _ (Empty_set _) (Singleton form A1)).
    { apply Extensionality_Ensembles. split. intro. intros. inversion H4. subst.
      apply Union_intror. split. subst. intros C HC ; inversion HC ; subst ; auto. inversion H4. }
    rewrite H4 in H3. clear H4.
    apply wBIH_Deduction_Theorem in H3. apply dual_residuation in H3.
    assert (prim (list_disj (remove eq_dec_form A2 x))).
    { apply Closed. eapply wMP. apply (wBIH_monot _ _ H3). intros C HC ; inversion HC.
      apply wId ; auto. }
    apply list_disj_prime in H4 ; auto. destruct H4. destruct H4.
    apply in_remove in H4 ; destruct H4.
    apply H1 in H4. inversion H4 ; subst. auto. inversion H7 ; subst ; auto.
    2: apply Prime. apply NotDer. }
  intros Hv. apply LEM_world in H0. destruct H0 as [w[Hw1 Hw2]].
  enough (exists v, Canon_rel v cp /\ wforces CM v A1 /\ ~ wforces CM v A2) by firstorder.
  exists w. split; try apply Hw1. unfold Canon_rel.
  intro. intros. apply Stable. intros Hx. pose (Hw2 x). simpl in i.
  assert (In form (Union form (Complement _ (@prim cp)) (Singleton form A2)) x).
  apply Union_introl. auto.
  apply i in H1. auto.
  split. apply IHA1. simpl. apply Hw1. apply In_singleton.
  intro. apply IHA2 in H0.
  assert (In _ (Union form (Complement form (@prim cp)) (Singleton form A2)) A2).
  apply Union_intror ; apply In_singleton ; auto. pose (Hw2 A2 H1).
  auto.
Qed.

Theorem wQuasiCompleteness: forall Γ A,
    ~ wBIH_prv Γ A -> ~ loc_conseq Γ A.
Proof.
intros Γ A WD H.
assert (~ wpair_der Γ (Singleton _ A)). intro. apply WD.
destruct H0. destruct H0. destruct H1. simpl in *. destruct x. simpl in H2. cbn in *.
eapply wMP. apply EFQ. auto.
simpl in H2. destruct x. simpl in H2. apply absorp_Or1 in H2 ; auto.
destruct (H1 f) ; cbn ; auto.
exfalso. destruct (H1 f) ; cbn ; auto. destruct (H1 f0) ; cbn ; auto.
inversion H0 ; subst. apply H5 ; cbn ; auto.
apply LEM_world in H0. destruct H0 as (w & H1 & H2).
apply (H2 A) ; auto. split. apply truth_lemma.
apply H.
intros B HB. apply truth_lemma ; auto.
Qed.

Theorem wCompleteness : forall (Γ : Ensemble _) A,
    loc_conseq Γ A -> wBIH_prv Γ A.
Proof.
intros Γ A LC. pose (wQuasiCompleteness Γ A).
destruct (LEM (wBIH_prv Γ A)) ; auto. exfalso.
apply n ; assumption.
Qed.

Theorem wSoundCompl : forall Γ A,
     wBIH_prv Γ A <-> loc_conseq Γ A.
Proof.
intros Γ A. split.
- apply LEM_wSoundness.
- apply wCompleteness.
Qed.

End LEM_completeness.

Print Assumptions wCompleteness.


  
