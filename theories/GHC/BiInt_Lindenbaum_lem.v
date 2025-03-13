Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Ensembles.
Require Import Syntax.
Require Import lems_remove_list.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import wBIH_meta_interactions.
Require Import BiInt_enum.
Require Import BiInt_Lindenbaum_lem_prelim.


(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* For any formula and context, either add the formula to the context, if the addition of
    the formula to the context preserve relative consistency, or keep the context as is. *)

Definition choice_form (Γ Δ : @Ensemble form) (A : form) : Ensemble form :=
fun x => (In _ Γ x) \/ ((wpair_der (Union _ Γ (Singleton _ A)) Δ) -> False) /\ A = x.

(* For any natural number, apply choice_form to the formula which it encodes. *)

Definition choice_code (Γ Δ : @Ensemble form) (n :nat) : @Ensemble form := 
          (choice_form Γ Δ (form_enum n)).

(* We build prime pairs by stages. We start with the initial pair, and add formulas to the
    left component by using the enumeration of formulas we have together with choice_code. *)

Fixpoint nprime_theory (Γ Δ : @Ensemble form) (n : nat) : @Ensemble form :=
match n with
| 0 => Γ
| S m => choice_code (nprime_theory Γ Δ m) Δ m
end.

(* We can thus define the left component of our pair: it is the collection of the left
    component of all the nprime_theory. Note that this theory would classically be
    a prime theory: this is why we call them prime_theory. *)

Definition prime_theory (Γ Δ : @Ensemble form) : @Ensemble form :=
  fun x => (exists n, In _ (nprime_theory Γ Δ n) x).

(* Then, we define some properties of sets of formulas, or pairs of sets of formulas. *)

Definition closed (Γ : @Ensemble (form)) :=
  forall A, wBIH_prv Γ A -> Γ A.

Definition stable (Γ : @Ensemble (form)) :=
  forall A, ~ ~ Γ A -> Γ A.

Definition prime (Γ : @Ensemble (form)) :=
  forall A B, Γ (Or A B) -> Γ A \/ Γ B.

Definition quasi_prime (Γ : @Ensemble (form)) :=
  forall A B, Γ (Or A B) -> ~ ~ (Γ A \/ Γ B).

(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* A helper lemma linking primeness and list_disj. *)

Lemma list_disj_prime : forall Γ,
  ~ (wBIH_prv Γ ( Bot)) ->
  prime Γ ->
  forall x, Γ (list_disj x) -> exists y, List.In y x /\ Γ y.
Proof.
intros Γ H. induction x ; simpl ; intros ; auto.
- exfalso ; auto. apply H. apply wId ; auto.
- apply H0 in H1. destruct H1 ; auto.
  + exists a ; split ; auto.
  + apply IHx in H1. destruct H1. destruct H1.
     exists x0 ; split ; auto.
Qed.

(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Properties of our prime theories, and the pairs built out of them. *)

(* A prime theory is an extension of the initial theory. *)

Lemma nprime_theory_extens : forall n (Γ Δ: @Ensemble form) x,
    In (form) Γ x -> In (form) (nprime_theory Γ Δ n) x.
Proof.
induction n.
- simpl. intros. unfold In. unfold choice_code. unfold choice_form. auto.
- simpl. intros. pose (IHn Γ Δ x H). unfold choice_code.
  unfold choice_form. simpl. unfold In ; auto.
Qed.

Lemma nprime_theory_extens_le : forall m n (Γ Δ: @Ensemble form) x,
    In (form) (nprime_theory Γ Δ n) x -> (le n m) -> In (form) (nprime_theory Γ Δ m) x.
Proof.
induction m.
- intros. simpl. inversion H0. subst. simpl in H. auto.
- intros. inversion H0.
  + subst. auto.
  + subst. simpl. unfold In. apply IHm in H ; auto. unfold choice_code.
     unfold choice_form. unfold In ; auto.
Qed.

Lemma prime_theory_extens : forall (Γ Δ: @Ensemble form) x,
    In (form) Γ x -> In (form) (prime_theory Γ Δ) x.
Proof.
intros. unfold prime_theory. unfold In. exists 0. unfold nprime_theory.
unfold choice_code. unfold choice_form ; auto.
Qed.

(* A prime theory preserves derivability. *)

Lemma der_nprime_theory_mprime_theory_le : forall n m (Γ Δ: @Ensemble form) A,
  wBIH_prv (nprime_theory Γ Δ n) A -> (le n m) ->
    wBIH_prv (nprime_theory Γ Δ m) A.
Proof.
intros.
pose (wBIH_monot (nprime_theory Γ Δ n) (A) H (nprime_theory Γ Δ m)).
simpl in w. apply w. intro. intros. apply nprime_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma der_prime_theory_nprime_theory : forall Γ Δ A, wBIH_prv (prime_theory Γ Δ) A ->
             exists n, wBIH_prv (nprime_theory Γ Δ n) A.
Proof.
intros Γ Δ A D. remember (prime_theory Γ Δ) as X. revert HeqX.
induction D ; intros ; subst.
- destruct H. exists x ; apply wId ; cbn ; auto.
- exists 0. apply wAx ; auto.
- destruct IHD1, IHD2 ; auto. exists (x + x0).
  eapply wMP. apply (der_nprime_theory_mprime_theory_le _ _ _ _ _ H). lia.
  apply (der_nprime_theory_mprime_theory_le _ _ _ _ _ H0). lia.
- exists 0. apply wDN ; auto.
Qed.

(* Each step of the construction preserves relative consistency. *)

Lemma Under_nprime_theory : forall n (Γ Δ: @Ensemble form), (wpair_der Γ Δ -> False) ->
  wpair_der (nprime_theory Γ Δ n) Δ -> False.
Proof.
induction n.
- intros. apply H. unfold nprime_theory in H0. auto.
- intros Γ Δ H. specialize (IHn _ _ H). intro.
  apply IHn. destruct H0. destruct H0. destruct H1. simpl in H1.
  apply wBIH_monot with (Γ1:=nprime_theory Γ Δ n) in H2. simpl in H2. exists x.
  repeat split ; auto. intros a Ha. simpl in Ha. unfold choice_code in Ha.
  simpl in H2. unfold choice_code in H2. unfold In. unfold choice_form in Ha.
  unfold choice_form in H2. unfold In in Ha. destruct Ha ; auto.
  destruct H3 ; subst. exfalso. apply H3. exists x. repeat split ; auto. simpl.
  apply wBIH_monot with (Γ1:=Union form (nprime_theory Γ Δ n) (Singleton form (form_enum n))) in H2 ; auto.
  intros b Hb. simpl in Hb. unfold In in Hb. destruct Hb. apply Union_introl ; auto.
  destruct H4 ; subst. apply Union_intror. apply In_singleton.
Qed.

(* The pair built out of a prime theory and the right component of the initial
   pair is relative consistent. *)

Lemma Under_Lind_pair_init : forall (Γ Δ: @Ensemble form), (wpair_der Γ ( Δ) -> False) ->
  wpair_der (prime_theory Γ Δ) Δ -> False.
Proof.
intros. destruct H0 as (l & Hl0 & Hl1 & Hl2).
epose (der_prime_theory_nprime_theory _ _ _ Hl2).
destruct e. pose (Under_nprime_theory x _ _ H). apply f.
exists l ; cbn ; auto.
Qed.

(* A prime pair is closed under derivation. *)

Lemma closeder_fst_Lind_pair : forall (Γ Δ: @Ensemble form), (wpair_der Γ ( Δ) -> False) -> closed (prime_theory Γ Δ).
Proof.
intros. intros A H0. unfold prime_theory. exists (S (form_index A)). unfold In.
remember (form_index A) as n. unfold nprime_theory. pose (form_enum_index A). destruct n.
-  unfold choice_form. right. split. intro. pose (Under_Lind_pair_init _ _ H). apply f.
   destruct H1. simpl in H1. destruct H1. destruct H2. exists x.
   repeat split ; auto. simpl.
   pose (wBIH_comp _ _ H3 (prime_theory Γ Δ)) as b. simpl in b. apply b.
   intros. inversion H4 ; subst. apply wId ; exists 0 ; auto.
   simpl. unfold choice_code. unfold choice_form. unfold In ; auto.
   inversion H5 ; subst ; auto. rewrite <- Heqn in e. rewrite e ; auto.
   rewrite Heqn ; auto.
- right. split. intro. pose (Under_Lind_pair_init _ _ H). apply f.
   destruct H1. simpl in H1. destruct H1. destruct H2. exists x.
   repeat split ; auto. simpl.
   pose (wBIH_comp _ _ H3 (prime_theory Γ Δ)) as b. simpl in b. apply b.
   intros. inversion H4 ; subst. apply wId ; exists (S n) ; auto.
   simpl. unfold choice_code. unfold choice_form. unfold In ; auto.
   inversion H5 ; subst ; auto. rewrite <- Heqn in e. rewrite e ; auto.
   rewrite Heqn ; auto.
Qed.

(* If a formula is not in the prime theory, then we know that not-not provability of the pair with the
    prime theory and the formula on the left, and the right component of the initial theory
    on the right, *)

Lemma not_In_prime_theory_deriv : forall (Γ Δ: @Ensemble form), (wpair_der Γ ( Δ) -> False) ->
  forall A, ~ (prime_theory Γ Δ A) -> ~~ (wpair_der (Union _ (prime_theory Γ Δ) (Singleton _ A)) Δ).
Proof.
intros. intro. apply H0. exists (S (form_index A)).
unfold nprime_theory. simpl. unfold In.
remember (form_index A) as n. pose (form_enum_index A). destruct n.
-  unfold choice_code. unfold choice_form. right ; split.
   intro. apply H1. destruct H2. simpl in H2. destruct H2. destruct H3.
   exists x. simpl ; repeat split ; auto.
   apply wBIH_monot with (Γ1:=Union form (prime_theory Γ Δ) (Singleton form A)) in H4 ; auto.
   intro. simpl ; intros. inversion H5 ; subst. apply Union_introl.
   exists 0 ; auto.
   apply Union_intror. rewrite <- Heqn in e. rewrite <- e. auto.
   rewrite Heqn ; auto.
-  right ; split.
   intro. apply H1. destruct H2. simpl in H2. destruct H2. destruct H3.
   exists x. simpl ; repeat split ; auto.
   apply wBIH_monot with (Γ1:=Union form (prime_theory Γ Δ) (Singleton form A)) in H4 ; auto.
   intro. simpl ; intros. inversion H5 ; subst. apply Union_introl.
   exists (S n) ; auto.
   apply Union_intror. rewrite <- Heqn in e. rewrite <- e. auto.
   rewrite Heqn ; auto.
Qed.

(* A prime theory is (constructively) quasi-prime. *)

Lemma quasi_prime_Lind_pair : forall (Γ Δ: @Ensemble form), (wpair_der Γ ( Δ) -> False) ->
  quasi_prime (prime_theory Γ Δ).
Proof.
intros. intros A B H0. intro.

assert (p: forall C, ~ ~ (prime_theory Γ Δ C \/ ~ (prime_theory Γ Δ C))).
intros C H2. apply H2. right. intro. apply H2 ; auto.

pose (p A). pose (p B). apply n. intro. destruct H2. apply H1 ; auto.
apply n0 ; intro. destruct H3. apply H1 ; auto.

apply not_In_prime_theory_deriv in H2 ; auto. apply H2. intro.
apply not_In_prime_theory_deriv in H3 ; auto. apply H3 ; intro.

apply Under_Lind_pair_init with (Γ:=Γ) (Δ:=Δ) ; auto.
destruct H4. simpl in H4. destruct H4. destruct H6.
destruct H5. simpl in H5. destruct H5. destruct H8.

exists (x ++ remove_list x x0). repeat split ; auto.
apply add_remove_list_preserve_NoDup ; auto.
simpl ; intros. apply in_app_or in H10. destruct H10 ; auto.
apply In_remove_list_In_list in H10 ; auto. simpl.
eapply wMP. eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity. subst ; cbn.
apply der_list_disj_remove1.
eapply wBIH_Deduction_Theorem. exact H7.
apply der_list_disj_remove2.
apply wBIH_Deduction_Theorem. exact H9.
apply wId ; auto.
Qed.

(* A prime theory is consistent. *)

Lemma Consist_nprime_theory : forall n (Γ Δ: @Ensemble form), (wpair_der Γ ( Δ) -> False) ->
  ~ wBIH_prv (nprime_theory Γ Δ n) Bot.
Proof.
intros. intro. pose (Under_nprime_theory n Γ Δ H).
apply f. exists []. repeat split ; auto. apply NoDup_nil.
intros. inversion H1.
Qed.

Lemma Consist_prime_theory : forall (Γ Δ: @Ensemble form), (wpair_der Γ Δ -> False) ->
  ~ wBIH_prv (prime_theory Γ Δ) Bot.
Proof.
intros. intro. apply closeder_fst_Lind_pair in H0 ; auto. unfold prime_theory in H0.
unfold In in H0. destruct H0. apply Consist_nprime_theory with (Γ:=Γ) (Δ:=Δ) (n:=x) ; auto.
apply wId ; auto.
Qed.


(* A prime pair is relative consistent. *)

Lemma Under_Lind_pair : forall (Γ Δ: @Ensemble form), (wpair_der Γ ( Δ) -> False) ->
  wpair_der (prime_theory Γ Δ) (Complement _ (prime_theory Γ Δ)) -> False.
Proof.
intros. destruct H0. destruct H0. destruct H1. simpl in H1. simpl in H2.
induction x.
- simpl in H2. pose (Consist_prime_theory _ _ H H2) ; auto.
- simpl in H2.
  pose (closeder_fst_Lind_pair _ _ H _ H2).
  pose (quasi_prime_Lind_pair _ _ H).
  simpl in p.  pose (q a (list_disj x) p). apply n. intro.
  destruct H3. assert (List.In a (a :: x)). apply in_eq. pose (H1 _ H4) ; auto.
  apply IHx. inversion H0 ; auto. intros. apply H1. apply in_cons ; auto.
  apply wId ; auto.
Qed.

(* The right component of a prime pair (the complement of the left component) is
    an extension of the right component of the initial pair. *)

Lemma Compl_prime_theory_extens : forall (Γ Δ: @Ensemble form) x,
     (wpair_der Γ ( Δ) -> False) -> In (form) Δ x -> In (form) (Complement _ (prime_theory Γ Δ)) x.
Proof.
intros. intros H1.
apply Under_Lind_pair_init with (Γ:=Γ) (Δ:=Δ) ; auto.
exists [x]. repeat split. apply NoDup_cons. intro. inversion H2.
apply NoDup_nil. simpl. intros. destruct H2 ; subst ; auto. exfalso ; auto.
simpl. eapply wMP.
apply wAx ; eapply A3 ; reflexivity.
apply wId ; auto.
Qed.

(* A prime pair is (left-)stable. *)

Lemma stable_Lind_pair : forall (Γ Δ: @Ensemble form), (wpair_der Γ ( Δ) -> False) ->
  stable (prime_theory Γ Δ).
Proof.
intros. intro. intros. exists (S (form_index A)).
unfold nprime_theory. unfold In.
remember (form_index A) as n. pose (form_enum_index A). destruct n.
-  unfold choice_code. unfold choice_form. right ; split.
   intro. apply H0. intro.
   apply Under_Lind_pair_init with (Γ:=Γ) (Δ:=Δ) ; auto. 
   destruct H1. simpl in H1. destruct H1. destruct H3.
   exists x. simpl ; repeat split ; auto.
   apply wBIH_monot with (Γ1:=(prime_theory Γ Δ)) in H4 ; auto.
   intro. simpl ; intros. inversion H5 ; subst. exists 1 ; auto.
   unfold nprime_theory. unfold choice_code. unfold choice_form. left ; auto.
   inversion H6 ; subst ; auto. rewrite <- Heqn in e. rewrite e. auto.
   rewrite Heqn ; auto.
-  unfold choice_code. unfold choice_form. right ; split.
   intro. apply H0. intro.
   apply Under_Lind_pair_init with (Γ:=Γ) (Δ:=Δ) ; auto. 
   destruct H1. simpl in H1. destruct H1. destruct H3.
   exists x. simpl ; repeat split ; auto.
   apply wBIH_monot with (Γ1:=(prime_theory Γ Δ)) in H4 ; auto.
   intro. simpl ; intros. inversion H5 ; subst. exists (S n) ; auto.
   inversion H6 ; subst ; auto. rewrite <- Heqn in e. rewrite e. auto.
   rewrite Heqn ; auto.
Qed.

(* A prime pair is (right-)stable. *)

Lemma right_stable_Lind_pair : forall (Γ Δ: @Ensemble form), (wpair_der Γ ( Δ) -> False) ->
  stable (Complement _ (prime_theory Γ Δ)).
Proof.
intros. intro. intros. intro. apply H0. intro. auto.
Qed.

(* Lindenbaum lemma. *)

Lemma Lindenbaum Γ Δ :
  ~ wpair_der Γ Δ ->
  exists Γm, Included _ Γ Γm
           /\ closed Γm
           /\ stable Γm
           /\ quasi_prime Γm
           /\ ~ wpair_der Γm Δ.
Proof.
intros.
exists (prime_theory Γ Δ).
repeat split.
- intro. apply prime_theory_extens.
- apply closeder_fst_Lind_pair ; auto.
- apply stable_Lind_pair ; auto.
- apply quasi_prime_Lind_pair ; auto.
- intro. apply Under_Lind_pair_init in H0 ; auto.
Qed.



