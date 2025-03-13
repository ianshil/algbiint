Require Import List.
Export ListNotations.

Require Import PeanoNat.

Require Import Ensembles.
Require Import Syntax.
Require Import BiInt_GHC.
Require Import BiInt_logics.

Lemma extens_diff_sBIH : forall (p : nat),
    sBIH_prv (Singleton _ (# p)) (¬ (∞ (# p))).
Proof.
intro p. eapply sDN. apply sId ; split.
Qed.

Theorem sBIH_extens_wBIH : forall Γ A,
    wBIH_prv Γ A -> sBIH_prv Γ A.
Proof.
intros Γ A D. induction D.
(* Id *)
- apply sId ; auto.
(* Ax *)
- apply sAx ; auto.
(* MP *)
- eapply sMP. exact IHD1. auto.
(* DN *)
- apply sDN. apply (sBIH_monot _ _ IHD). intros B HB ; inversion HB.
Qed.

Theorem pair_sBIH_extens_wBIH : forall Γ Δ,
    wpair_der Γ Δ -> spair_der Γ Δ.
Proof.
intros Γ Δ wpair. destruct wpair as (l & Hl0 & Hl1 & Hl2).
exists l ; repeat split ; auto. apply sBIH_extens_wBIH ; auto.
Qed.

Theorem sBIH_wBIH_same_thms : forall A,
    sBIH_prv (Empty_set _) A <-> wBIH_prv (Empty_set _) A.
Proof.
intros A. split.
- intro D ; remember (Empty_set form) as X ; revert HeqX ; induction D ; intro ; subst.
  (* Id *)
  + inversion H.
  (* Ax *)
  + apply wAx ; auto.
  (* MP *)
  + eapply wMP. apply IHD1 ; auto. apply IHD2 ; auto.
  (* sDN *)
  + apply wDN ; auto.
- intro D ; remember (Empty_set form) as X ; revert HeqX ; induction D ; intro ; subst.
  (* Id *)
  + inversion H.
  (* Ax *)
  + apply sAx ; auto.
  (* MP *)
  + eapply sMP. apply IHD1 ; auto. apply IHD2 ; auto.
  (* wDN *)
  + apply sDN ; auto.
Qed.

