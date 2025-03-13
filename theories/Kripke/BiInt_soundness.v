Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Syntax.
Require Import BiInt_GHC.
Require Import wBIH_meta_interactions.
Require Import BiInt_Kripke_sem.


Definition wSoundness := forall Γ A, wBIH_prv Γ A -> loc_conseq Γ A.

Definition sSoundness := forall Γ A, sBIH_prv Γ A -> glob_conseq Γ A.

Section Soundness_LEM.

Lemma list_disj_witn : forall M w l,
    (wforces M w (list_disj l)) ->
    (exists A, (List.In A l) /\ wforces M w A).
Proof.
induction l.
- simpl. intros. inversion H.
- simpl. intros. destruct H.
  * exists a. split. apply in_eq. assumption.
  * apply IHl in H. destruct H. destruct H. exists x. split ; try assumption. apply in_cons ; auto.
Qed.

Axiom LEM : forall P, P \/ ~ P.

(* LEM implies soundness  *)

Lemma wforces_dec : forall A M w,
    (wforces M w A) \/ ((wforces M w A) -> False).
Proof.
intros. apply LEM.
Qed.

(* To get rid of the decidability of forcing we could change the semantics of the
    disjunction, by adding a double negation. *)

Lemma Ax_valid : forall A, Axioms A ->
  (forall M w, wforces M w A).
Proof.
intros A Ax. inversion Ax ; subst ; cbn ; intros ; auto ; try contradiction.
- apply Persistence with v ; auto.
- apply H0 with v1 ; auto. apply reach_tran with v0 ; auto.
  apply reach_refl.
- destruct H4 ; auto. apply H0 in H4 ; auto. apply reach_tran with v0 ; auto.
- destruct H0 ; auto.
- destruct H0 ; auto.
- split ; auto. apply H0 ; auto. apply reach_tran with v0 ; auto.
- pose (@wforces_dec B M v).
  destruct o ; auto. right. intro. apply H1, H2; trivial. apply reach_refl.
- intro. apply H0. intros. apply H1 with v0; trivial. apply reach_refl.
- intro. apply H0. intros. pose (@wforces_dec C M v0). destruct o ; auto. exfalso.
  assert (~ ~ ((exists v, reachable v v0 /\ wforces M v A0 /\ ~ wforces M v B) \/ ~ (exists v, reachable v v0 /\ wforces M v A0 /\ ~ wforces M v B))) by tauto.
  apply H5. intros [(v1 & H6 & H7 & H8)|H6].
  + apply H1 in H7 as [H7|H7]; try tauto.
    * apply H4. now apply Persistence with v1.
    * now apply reach_tran with v0.
  + apply H3. intros. pose (@wforces_dec B M v1).
    destruct o. auto. contradict H6. now exists v1.
- pose (@H0 v0 H1). pose (@wforces_dec B M v0).
  destruct o ; auto.
  exfalso. apply f. intro. apply H3, H4; trivial. apply reach_refl.
Qed.

Theorem LEM_wSoundness : forall Γ A, wBIH_prv Γ A -> loc_conseq Γ A.
Proof.
intros Γ A D. induction D ; intros M w Hw ; auto.
(* Ax *)
- apply Ax_valid ; assumption.
(* MP *)
- apply (IHD1 M w Hw). apply reach_refl.
  apply (IHD2 M w Hw).
(* wDN *)
- intros v H H0 ; cbn. apply H0. intros.
  apply (IHD M v0). intros C HC ; inversion HC.
Qed.

Theorem LEM_sSoundness : forall Γ A, sBIH_prv Γ A -> glob_conseq Γ A.
Proof.
intros Γ A D. induction D ; intros M HM ; auto.
(* Ax *)
- intro w. apply Ax_valid ; assumption.
(* MP *)
- intro w. apply (IHD1 M HM w). apply reach_refl.
  apply (IHD2 M HM w).
(* sDN *)
- intros v v0 H H0 ; cbn. apply H0. intros.
  apply (IHD M HM).
Qed.

Print Assumptions LEM_wSoundness.

End Soundness_LEM.


