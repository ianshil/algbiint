Require Import List.
Export ListNotations.

Require Import PeanoNat.

Require Import Ensembles.
Require Import Syntax.
Require Import BiInt_GHC.

Theorem wBIH_monot : forall Γ A,
          wBIH_prv Γ A ->
          forall Γ1, (Included _ Γ Γ1) ->
          wBIH_prv Γ1 A.
Proof.
intros Γ A D0. induction D0 ; intros Γ1 incl.
(* Id *)
- apply wId ; auto.
(* Ax *)
- apply wAx ; auto.
(* MP *)
- apply wMP with A ; auto.
(* wDN *)
- apply wDN ; auto.
Qed.

Theorem sBIH_monot : forall Γ A,
          sBIH_prv Γ A ->
          forall Γ1, (Included _ Γ Γ1) ->
          sBIH_prv Γ1 A.
Proof.
intros Γ A D0. induction D0 ; intros Γ1 incl.
(* Id *)
- apply sId ; auto.
(* Ax *)
- apply sAx ; auto.
(* MP *)
- apply sMP with A ; auto.
(* sDN *)
- apply sDN ; auto.
Qed.

Theorem wBIH_comp : forall Γ A,
          wBIH_prv Γ A ->
          forall Γ', (forall B, Γ B -> wBIH_prv Γ' B) ->
          wBIH_prv Γ' A.
Proof.
intros Γ A D0. induction D0 ; intros Γ' derall ; auto.
(* Ax *)
- apply wAx ; auto.
(* MP *)
- apply wMP with A ; auto.
(* wDN *)
- apply wDN ; auto.
Qed.

Theorem sBIH_comp : forall Γ A,
          sBIH_prv Γ A ->
          forall Γ', (forall B, Γ B -> sBIH_prv Γ' B) ->
          sBIH_prv Γ' A.
Proof.
intros Γ A D0. induction D0 ; intros Γ' derall ; auto.
(* Ax *)
- apply sAx ; auto.
(* MP *)
- apply sMP with A ; auto.
(* sDN *)
- apply sDN ; auto.
Qed.

Lemma subst_Ax : forall A f, (Axioms A) -> (Axioms (subst f A)).
Proof.
intros A f Ax.
destruct Ax ; subst ; [ eapply A1 ; reflexivity | eapply A2 ; reflexivity | eapply A3 ; reflexivity |
eapply A4 ; reflexivity | eapply A5 ; reflexivity | eapply A6 ; reflexivity |
eapply A7 ; reflexivity | eapply A8 ; reflexivity | eapply A9 ; reflexivity | eapply A10 ; reflexivity |
eapply BA1 ; reflexivity | eapply BA2 ; reflexivity | eapply BA3 ; reflexivity | eapply BA4 ; reflexivity].
Qed.

Theorem wBIH_struct : forall Γ A f,
  (wBIH_prv Γ A) ->
  wBIH_prv (fun x : form => exists B, x = subst f B /\ Γ B) (subst f A).
Proof.
intros Γ A f D. revert f. induction D ; cbn ; intro f.
(* Id *)
- apply wId ; exists A ; auto.
(* Ax *)
- apply wAx ; apply subst_Ax ; auto.
(* MP *)
- eapply wMP. apply IHD1 ; auto. apply IHD2 ; auto.
(* wDN *)
- apply wDN. apply (wBIH_monot _ _ (IHD f)) ; auto.
  intros C HC. destruct HC as (B & HB0 & HB1) ; inversion HB1.
Qed.

Theorem sBIH_struct : forall Γ A f,
  (sBIH_prv Γ A) ->
  sBIH_prv (fun x : form => exists B, x = subst f B /\ Γ B) (subst f A).
Proof.
intros Γ A f D. revert f. induction D ; cbn ; intro f.
(* Id *)
- apply sId ; exists A ; auto.
(* Ax *)
- apply sAx ; apply subst_Ax ; auto.
(* MP *)
- eapply sMP. apply IHD1 ; auto. apply IHD2 ; auto.
(* wDN *)
- apply sDN. apply (sBIH_monot _ _ (IHD f)) ; auto.
  intros C HC ; auto.
Qed.

Theorem wBIH_finite : forall Γ A,
          (wBIH_prv Γ A) ->
          exists Fin, Included _ Fin Γ /\
                          wBIH_prv Fin A /\
                          exists l, forall A, (Fin A -> List.In A l) * (List.In A l -> Fin A).
Proof.
intros Γ A D0. induction D0.
(* Id *)
- exists (fun x => x = A). repeat split.
  intros C HC ; inversion HC ; auto.
  apply wId ; unfold In ; auto.
  exists [A]. intro ; split ; intro ; subst. apply in_eq.
  inversion H0 ; auto. inversion H1.
(* Ax *)
- exists (Empty_set _). repeat split.
  intros C HC ; inversion HC.
  apply wAx ; auto.
  exists []. intro ; split ; intro H0 ; inversion H0.
(* MP *)
- destruct IHD0_1 as (Fin0 & HF00 & HF01 & (l0 & Hl0)) ;
  destruct IHD0_2 as (Fin1 & HF10 & HF11 & (l1 & Hl1)).
  exists (Union _ Fin0 Fin1). repeat split.
  intros C HC ; inversion HC ; auto.
  eapply wMP. apply (wBIH_monot _ _ HF01).
  intros C HC ; left ; auto.
  apply (wBIH_monot _ _ HF11). intros C HC ; right ; auto.
  exists (l0 ++ l1). intro C ; split ; intro H. apply in_or_app.
  inversion H ; subst ; firstorder. apply in_app_or in H ; destruct H.
  left ; firstorder. right ; firstorder.
(* wDN *)
- destruct IHD0 as (Fin0 & HF00 & HF01 & (l0 & Hl0)). exists (Empty_set _). repeat split.
  intros B HB ; inversion HB. apply wDN ; auto. exists []. intro B. split ; intro HB ; inversion HB.
Qed.

Theorem sBIH_finite : forall Γ A,
          (sBIH_prv Γ A) ->
          exists Fin, Included _ Fin Γ /\
                          sBIH_prv Fin A /\
                          exists l, forall A, (Fin A -> List.In A l) * (List.In A l -> Fin A).
Proof.
intros Γ A D0. induction D0.
(* Id *)
- exists (fun x => x = A). repeat split.
  intros C HC ; inversion HC ; auto.
  apply sId ; unfold In ; auto.
  exists [A]. intro ; split ; intro ; subst. apply in_eq.
  inversion H0 ; auto. inversion H1.
(* Ax *)
- exists (Empty_set _). repeat split.
  intros C HC ; inversion HC.
  apply sAx ; auto.
  exists []. intro ; split ; intro H0 ; inversion H0.
(* MP *)
- destruct IHD0_1 as (Fin0 & HF00 & HF01 & (l0 & Hl0)) ;
  destruct IHD0_2 as (Fin1 & HF10 & HF11 & (l1 & Hl1)).
  exists (Union _ Fin0 Fin1). repeat split.
  intros C HC ; inversion HC ; auto.
  eapply sMP. apply (sBIH_monot _ _ HF01).
  intros C HC ; left ; auto.
  apply (sBIH_monot _ _ HF11). intros C HC ; right ; auto.
  exists (l0 ++ l1). intro C ; split ; intro H. apply in_or_app.
  inversion H ; subst ; firstorder. apply in_app_or in H ; destruct H.
  left ; firstorder. right ; firstorder.
(* wDN *)
- destruct IHD0 as (Fin0 & HF00 & HF01 & (l0 & Hl0)).
  exists Fin0. repeat split.
  intros B HB ; auto.
  apply sDN ; auto. exists l0 ; auto.
Qed.

