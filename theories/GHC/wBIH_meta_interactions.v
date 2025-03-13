Require Import List.
Export ListNotations.

Require Import genT.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Syntax.
Require Import lems_remove_list.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import BiInt_extens_interactions.

Section properties.

Lemma Thm_irrel : forall A B Γ, wBIH_prv Γ (A --> (B --> A)).
Proof.
intros A B Γ. apply wAx ; eapply A1 ; reflexivity.
Qed.

Lemma imp_Id_gen : forall A Γ, wBIH_prv Γ (A --> A).
Proof.
intros.
eapply wMP. eapply wMP.
apply wAx ; eapply A2 ; reflexivity.
apply wAx ; eapply A1 ; reflexivity.
eapply wMP.
apply wAx ; eapply A1 ; reflexivity.
apply wAx ; apply A1 with (⊥ --> ⊥) ⊥ ; reflexivity.
Qed.

Lemma comm_And_obj : forall A B Γ,
    wBIH_prv Γ ((A ∧ B) --> (B ∧ A)).
Proof.
intros A B Γ. eapply wMP. eapply wMP.
apply wAx ; eapply A8 ; reflexivity.
apply wAx ; eapply A7 ; reflexivity.
apply wAx ; eapply A6 ; reflexivity.
Qed.

Lemma comm_Or_obj : forall A B Γ, wBIH_prv Γ (A ∨ B -->  B ∨ A).
Proof.
intros A B Γ. eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity.
apply wAx ; eapply A4 ; reflexivity.
apply wAx ; eapply A3 ; reflexivity.
Qed.

Lemma comm_Or : forall A B Γ, wBIH_prv Γ (A ∨ B) -> wBIH_prv Γ (B ∨ A).
Proof.
intros A B Γ D. eapply wMP. apply comm_Or_obj. auto.
Qed.

Lemma EFQ : forall A Γ, wBIH_prv Γ (⊥ -->  A).
Proof.
intros A Γ. apply wAx. eapply A9 ; reflexivity.
Qed.

Lemma Imp_trans_help7 : forall x y z Γ, wBIH_prv Γ ((x --> (y --> (z --> y)))).
Proof.
intros. eapply  wMP. all: apply wAx ; eapply A1 ; reflexivity.
Qed.

Lemma Imp_trans_help8 : forall x y z Γ,
  wBIH_prv Γ ((((x --> (y --> z)) --> (x --> y)) --> ((x --> (y --> z)) --> (x --> z)))).
Proof.
intros. eapply  wMP. all: apply wAx ; eapply A2 ; reflexivity.
Qed.

Lemma Imp_trans_help9 : forall x y z u Γ,
  wBIH_prv Γ ((x --> ((y --> (z --> u)) --> ((y --> z) --> (y --> u))))).
Proof.
intros. eapply  wMP. all: apply wAx.
eapply A1 ; reflexivity. eapply A2 ; reflexivity.
Qed.

Lemma Imp_trans_help14 : forall x y z u Γ,
  wBIH_prv Γ ((x --> (y --> (z --> (u --> z))))).
Proof.
intros. eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help35 : forall x y z Γ, wBIH_prv Γ ((x --> ((y --> x) --> z)) --> (x --> z)).
Proof.
intros. eapply  wMP. apply Imp_trans_help8. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help37 : forall x y z u Γ, wBIH_prv Γ (((x --> ((y --> (z --> y)) --> u)) --> (x --> u))).
Proof.
intros. eapply  wMP. apply Imp_trans_help8. apply Imp_trans_help14.
Qed.

Lemma Imp_trans_help54 : forall x y z u Γ,
  wBIH_prv Γ ((((x --> (y --> z)) --> (((x --> y) --> (x --> z)) --> u)) --> ((x --> (y --> z)) --> u))).
Proof.
intros. eapply  wMP. apply Imp_trans_help8. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help170 : forall x y z Γ, wBIH_prv Γ ((x --> y) --> ((z --> x) --> (z --> y))).
Proof.
intros. eapply  wMP. apply Imp_trans_help35. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help410 : forall x y z Γ,
  wBIH_prv Γ ((((x --> y) --> z) --> (y --> z))).
Proof.
intros. eapply wMP. apply Imp_trans_help37. apply Imp_trans_help170.
Qed.

Lemma Imp_trans_help427 : forall x y z u Γ,
  wBIH_prv Γ ((x --> (((y --> z) --> u) --> (z --> u)))).
Proof.
intros. eapply  wMP. apply wAx ; eapply A1 ; reflexivity. apply Imp_trans_help410.
Qed.

Lemma Imp_trans : forall A B C Γ, wBIH_prv Γ ((A --> B) -->  (B --> C) --> (A --> C)).
Proof.
intros. eapply  wMP. eapply  wMP. apply Imp_trans_help54. apply Imp_trans_help427.
apply Imp_trans_help170.
Qed.

Lemma meta_Imp_trans : forall A B C Γ, wBIH_prv Γ (A --> B) -> wBIH_prv Γ (B --> C) ->
                wBIH_prv Γ (A --> C).
Proof.
intros A B C Γ H H0. eapply wMP. 
- eapply wMP.
  + eapply Imp_trans.
  + exact H.
- auto.
Qed.

Lemma assoc_And_obj : forall A B C Γ, wBIH_prv Γ (A ∧ B ∧ C --> (A ∧ B) ∧ C) /\ 
                                      wBIH_prv Γ ((A ∧ B) ∧ C --> A ∧ B ∧ C).
Proof.
intros A B C Γ. split.
- eapply wMP.
  + eapply wMP.
    * apply wAx ; eapply A8 ; reflexivity.
    * eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ apply wAx ; eapply A6 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ apply wAx ; eapply A7 ; reflexivity.
        ++ apply wAx ; eapply A6 ; reflexivity.
  + eapply meta_Imp_trans.
    * apply wAx ; eapply A7 ; reflexivity.
    * apply wAx ; eapply A7 ; reflexivity.
- eapply wMP.
  + eapply wMP.
    * apply wAx ; eapply A8 ; reflexivity.
    * eapply meta_Imp_trans.
      -- apply wAx ; eapply A6 ; reflexivity.
      -- apply wAx ; eapply A6 ; reflexivity.
  + eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ apply wAx ; eapply A6 ; reflexivity.
        ++ apply wAx ; eapply A7 ; reflexivity.
    * apply wAx ; eapply A7 ; reflexivity.
Qed.

Lemma monotR_Or : forall A B Γ ,
    wBIH_prv Γ (A -->  B) ->
    forall C, wBIH_prv Γ ((A ∨ C) -->  (B ∨ C)).
Proof.
intros A B Γ D C. eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity.
eapply wMP. eapply wMP. apply Imp_trans. exact D.
apply wAx ; eapply A3 ; reflexivity.
apply wAx ; eapply A4 ; reflexivity.
Qed.

Lemma monotL_Or : forall A B Γ,
    wBIH_prv Γ (A -->  B) ->
    forall C, wBIH_prv Γ ((C ∨ A) -->  (C ∨ B)).
Proof.
intros A B Γ D C. eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity.
apply wAx ; eapply A3 ; reflexivity.
eapply wMP. eapply wMP. apply Imp_trans. exact D.
apply wAx ; eapply A4 ; reflexivity.
Qed.

Lemma monot_Or2 : forall A B Γ, wBIH_prv Γ (A -->  B) ->
    forall C, wBIH_prv Γ ((A ∨ C) -->  (C ∨ B)).
Proof.
intros A B Γ D C.
eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity.
eapply wMP. eapply wMP. apply Imp_trans. exact D.
apply wAx ; eapply A4 ; reflexivity.
apply wAx ; eapply A3 ; reflexivity.
Qed.

Lemma prv_Top : forall Γ , wBIH_prv Γ ⊤.
Proof.
intros. eapply wMP. apply wAx ; apply A10 with (⊤ --> ⊤) ; reflexivity. apply imp_Id_gen.
Qed.

Lemma absorp_Or1 : forall A Γ ,
    wBIH_prv Γ (A ∨ ⊥) ->
    wBIH_prv Γ A.
Proof.
intros A Γ D. eapply wMP. eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity.
apply imp_Id_gen. apply EFQ. auto.
Qed.

Lemma absorp_Or2 : forall A Γ ,
    wBIH_prv Γ (⊥ ∨ A) ->
    wBIH_prv Γ A.
Proof.
intros A Γ D. eapply wMP. eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity.
apply EFQ. apply imp_Id_gen. auto.
Qed.

Lemma Imp_And : forall A B C Γ, wBIH_prv Γ ((A -->  (B -->  C)) --> ((A ∧ B) -->  C)).
Proof.
intros A B C Γ. eapply wMP. eapply wMP. apply Imp_trans. eapply wMP. apply Imp_trans.
apply wAx ; eapply A6 ; reflexivity.
eapply wMP. eapply wMP.
apply wAx ; eapply A2 ; reflexivity.
apply wAx ; eapply A2 ; reflexivity.
eapply wMP.
apply wAx ; eapply A1 ; reflexivity.
apply wAx ; eapply A7 ; reflexivity.
Qed.

Lemma Contr_Bot : forall A Γ, wBIH_prv Γ (A ∧ (¬ A) -->  (⊥)).
Proof.
intros A Γ . eapply wMP. eapply wMP. apply Imp_trans.
apply comm_And_obj. eapply wMP. apply Imp_And.
apply imp_Id_gen.
Qed.

(* The next proof is rather obscure, as it was generated by prover9. *)

Lemma And_Imp : forall A B C Γ, wBIH_prv Γ (((A ∧ B) -->  C) --> (A --> (B -->  C))).
Proof.
intros.
eapply wMP.
- eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. eapply wMP.
  1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity.
- eapply wMP.
  { eapply wMP. eapply wMP. eapply wMP. eapply wMP.
  eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP.
  apply wAx ; eapply A1 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity. eapply wMP. eapply wMP.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP.
  apply wAx ; eapply A1 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity. eapply wMP. eapply wMP.
  eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity. eapply wMP.
  eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP. apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. eapply wMP. apply wAx ; eapply A8 ; reflexivity. eapply wMP. eapply wMP.
  apply wAx ; eapply A2 ; reflexivity. apply wAx ; eapply A1 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. eapply wMP.
  1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity. eapply wMP.
  eapply wMP. apply wAx ; eapply A2 ; reflexivity. eapply wMP. apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity. apply wAx ; eapply A7 ; reflexivity.
  apply wAx ; eapply A6 ; reflexivity. eapply wMP. eapply wMP.
  eapply wMP. apply wAx ; eapply A2 ; reflexivity. apply wAx ; eapply A8 ; reflexivity. eapply wMP.
  apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A7 ; reflexivity. eapply wMP. eapply wMP.
  eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity. eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A6 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity. eapply wMP. apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity. apply wAx ; eapply A8 ; reflexivity. eapply wMP.
  apply wAx ; eapply A1 ; reflexivity. eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity. apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity. }
  { eapply wMP. eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. eapply wMP.
  1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity. 
  eapply wMP. eapply wMP. eapply wMP. 1-2: apply wAx ; eapply A2 ; reflexivity.
  eapply wMP. 1-2: apply wAx ; eapply A1 ; reflexivity.
  eapply wMP. apply wAx ; eapply A1 ; reflexivity. apply wAx ; eapply A2 ; reflexivity. }
Unshelve. all: auto.
Qed.

Theorem wBIH_Detachment_Theorem : forall A B Γ,
           wBIH_prv Γ (A --> B) ->
           wBIH_prv  (Union _ Γ  (Singleton _ (A))) B.
Proof.
intros A B Γ D. eapply wMP. apply (wBIH_monot Γ (A --> B)) ; auto.
intros C HC. apply Union_introl ; auto.
apply wId. apply Union_intror. apply In_singleton.
Qed.

Theorem wBIH_Deduction_Theorem : forall A B Γ,
           wBIH_prv (Union _ Γ  (Singleton _ (A))) B ->
           wBIH_prv Γ (A -->  B).
Proof.
intros. remember (Union form Γ (Singleton form A)) as L.
revert L B H A Γ HeqL.
intros L B D. induction D ; intros C Γ0 id ; subst.
(* wId *)
- inversion H ; subst ; cbn.
  + eapply wMP. apply Thm_irrel. apply wId ; auto.
  + inversion H0 ; subst. apply imp_Id_gen.
(* wAx *)
- eapply wMP. apply Thm_irrel. apply wAx ; assumption.
(* wMP *)
- eapply wMP. eapply wMP. apply Imp_trans. eapply wMP.
  eapply wMP. apply wAx ; eapply A8 ; reflexivity. apply imp_Id_gen.
  apply IHD2 ; auto. eapply wMP. apply Imp_And. apply IHD1 ; auto.
(* wDN *)
- eapply wMP. apply Thm_irrel. apply wDN ; auto.
Qed.

Theorem gen_wBIH_Detachment_Theorem : forall A B Γ,
  wpair_der Γ (Singleton _ (A --> B)) ->
      wpair_der (Union form Γ (Singleton form A))  (Singleton _ B).
Proof.
intros A B Γ wpair. unfold wpair_der. exists [B]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. cbn. apply In_singleton. inversion H0.
cbn. eapply wMP. apply wAx ; eapply A3 ; reflexivity.
destruct wpair as (l & Hl0 & Hl1 & Hl2). destruct l ; cbn in *.
eapply wMP. apply EFQ. apply (wBIH_monot _ _ Hl2).
intros C HC ; left ; auto.
destruct l. cbn in *. assert (Singleton form (A --> B) f). apply Hl1 ; auto.
inversion H ; subst. apply absorp_Or1 in Hl2. apply wBIH_Detachment_Theorem in Hl2 ; auto.
exfalso. cbn in *. assert (Singleton form (A --> B) f). apply Hl1 ; auto.
assert (Singleton form (A --> B) f0). apply Hl1 ; auto. inversion H ; subst.
inversion H0 ; subst. inversion Hl0 ; subst. apply H3 ; apply in_eq.
Qed.

Theorem gen_wBIH_Deduction_Theorem : forall A B Γ,
  wpair_der (Union form Γ (Singleton form A)) (Singleton _ B) ->
      wpair_der Γ (Singleton _ (A --> B)).
Proof.
intros A B Γ wpair. unfold wpair_der. cbn. exists [(A --> B)]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. apply In_singleton. inversion H0.
eapply wMP. apply wAx ; eapply A3 ; reflexivity.
apply wBIH_Deduction_Theorem.
destruct wpair as (l & Hl0 & Hl1 & Hl2). destruct l ; cbn in *.
eapply wMP. apply EFQ. auto.
destruct l. cbn in *. assert (Singleton form B f). apply Hl1 ; auto.
inversion H ; subst. apply absorp_Or1 in Hl2 ; auto.
exfalso. cbn in *. assert (Singleton form B f). apply Hl1 ; auto.
assert (Singleton form B f0). apply Hl1 ; auto. inversion H ; subst.
inversion H0 ; subst. inversion Hl0 ; subst. apply H3 ; apply in_eq.
Qed.








Section remove_stuff.

Lemma In_remove : forall (A : form) B (l : list (form)), List.In A (remove eq_dec_form B l) -> List.In A l.
Proof.
intros A B. induction l.
- cbn. auto.
- intro. cbn in H. destruct (eq_dec_form B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + subst. apply in_cons. apply IHl. auto.
Qed.

Lemma InT_remove : forall (A : form) B (l : list (form)), InT A (remove eq_dec_form B l) -> InT A l.
Proof.
intros A B. induction l.
- cbn. auto.
- intro. cbn in H. destruct (eq_dec_form B a).
  * subst. apply InT_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply InT_eq.
    + subst. apply InT_cons. apply IHl. auto.
Qed.

Lemma NoDup_remove : forall A (l : list (form)), NoDup l -> NoDup (remove eq_dec_form A l).
Proof.
intro A. induction l.
- intro. cbn. apply NoDup_nil.
- intro H. cbn. destruct (eq_dec_form A a).
  * subst. apply IHl. inversion H. assumption.
  * inversion H. subst. apply NoDup_cons. intro. apply H2. apply In_remove with (B:= A).
    assumption. apply IHl. assumption.
Qed.

Lemma remove_disj : forall l B Γ, wBIH_prv Γ (list_disj l --> B ∨ (list_disj (remove eq_dec_form B l))).
Proof.
induction l.
- intros. cbn. apply wAx ; eapply A4 ; reflexivity.
- intros. pose (IHl B Γ). cbn. destruct (eq_dec_form B a).
  * subst. cbn. eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
    apply wAx ; eapply A3 ; reflexivity. auto.
  * cbn. eapply wMP. eapply wMP. apply Imp_trans. eapply wMP. eapply wMP.
    apply wAx ; eapply A5 ; reflexivity. apply wAx ; eapply A3 ; reflexivity.
    eapply wMP. eapply wMP. apply Imp_trans. auto. apply wAx ; eapply A4 ; reflexivity.
    eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity. eapply wMP. eapply wMP.
    apply Imp_trans. apply wAx ; eapply A3 ; reflexivity. apply wAx ; eapply A4 ; reflexivity.
    apply monotL_Or. apply wAx ; eapply A4 ; reflexivity.
Qed.

End remove_stuff.







Section list_disj_stuff.

Lemma Id_list_disj : forall Γ l0 l1,
  wBIH_prv Γ (list_disj l0 --> list_disj (l0 ++ l1)).
Proof.
induction l0 ; intros.
- cbn. apply EFQ.
- cbn. apply monotL_Or. apply IHl0.
Qed.

Lemma list_disj_app : forall l0 Γ A l1,
  wBIH_prv Γ (A --> list_disj (l0 ++ l1)) -> wBIH_prv Γ (A --> ((list_disj l0) ∨ (list_disj l1))).
Proof.
induction l0.
- cbn. intros. eapply wMP. eapply wMP. apply Imp_trans. exact H.
  apply wAx ; eapply A4 ; reflexivity.
- cbn. intros. eapply wMP. eapply wMP. apply Imp_trans. exact H. eapply wMP.
  eapply wMP. apply Imp_trans. apply monotL_Or. apply IHl0. apply imp_Id_gen.
  eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
  eapply wMP. eapply wMP. apply Imp_trans. apply wAx ; eapply A3 ; reflexivity.
  apply wAx ; eapply A3 ; reflexivity. apply monotR_Or.
  apply wAx ; eapply A4 ; reflexivity.
Qed.

Lemma list_disj_app0 : forall l0 Γ A l1,
  wBIH_prv Γ (A --> ((list_disj l0) ∨ (list_disj l1))) -> wBIH_prv Γ (A --> list_disj (l0 ++ l1)).
Proof.
induction l0.
- cbn. intros. eapply wMP. eapply wMP. apply Imp_trans. exact H. eapply wMP.
  eapply wMP. apply wAx ; eapply A5 ; reflexivity. apply EFQ. apply imp_Id_gen.
- cbn. intros. eapply wMP. eapply wMP. apply Imp_trans. exact H. eapply wMP.
  eapply wMP. apply Imp_trans. eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
  apply monotL_Or. apply wAx ; eapply A3 ; reflexivity. eapply wMP. eapply wMP.
  apply Imp_trans. apply wAx ; eapply A4 ; reflexivity. apply wAx ; eapply A4 ; reflexivity.
  apply monotL_Or. apply IHl0. apply imp_Id_gen.
Qed.

Lemma list_disj_remove_app : forall l0 l1 Γ A,
wBIH_prv Γ (list_disj (l0 ++ remove_list l0 l1) --> A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove_list l0 l1)))).
Proof.
induction l0 ; cbn ; intros.
- apply remove_disj.
- eapply wMP. eapply wMP. apply Imp_trans. apply monotL_Or. eapply wMP.
  eapply wMP. apply Imp_trans. eapply wMP. eapply wMP. apply Imp_trans.
  eapply wMP. eapply wMP. apply Imp_trans. apply list_disj_app. apply imp_Id_gen.
  apply monotL_Or. apply remove_disj. eapply wMP. eapply wMP.
  apply wAx ; eapply A5 ; reflexivity. eapply wMP. eapply wMP. apply Imp_trans.
  apply wAx ; eapply A3 ; reflexivity. apply wAx ; eapply A4 ; reflexivity.
  apply monotL_Or. apply wAx ; eapply A4 ; reflexivity.
  apply monotL_Or. apply list_disj_app0. apply imp_Id_gen. 
  eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
  eapply wMP. eapply wMP. apply Imp_trans.
  apply wAx ; eapply A3 ; reflexivity. apply wAx ; eapply A4 ; reflexivity.
  apply monotL_Or. apply wAx ; eapply A4 ; reflexivity.
Qed.

Lemma Id_list_disj_remove : forall Γ l0 l1,
  wBIH_prv Γ (list_disj l1 --> list_disj (l0 ++ remove_list l0 l1)).
Proof.
induction l0 ; cbn ; intros.
- apply imp_Id_gen.
- eapply wMP. eapply wMP. apply Imp_trans. apply IHl0. apply list_disj_remove_app.
Qed.

Lemma der_list_disj_remove1 : forall Γ A l0 l1,
    wBIH_prv Γ (A --> list_disj l0) ->
    wBIH_prv Γ (A --> list_disj (l0 ++ remove_list l0 l1)).
Proof.
intros Γ A. induction l0 ; cbn in * ; intros.
- eapply wMP. eapply wMP. apply Imp_trans. exact H. apply EFQ.
- eapply wMP. eapply wMP. apply Imp_trans. exact H. apply monotL_Or.
  apply Id_list_disj.
Qed.

Lemma der_list_disj_remove2 : forall Γ A l0 l1,
    wBIH_prv Γ (A --> list_disj l1) ->
    wBIH_prv Γ (A --> list_disj (l0 ++ remove_list l0 l1)).
Proof.
intros. eapply wMP. eapply wMP. apply Imp_trans. exact H.
eapply wMP. eapply wMP. apply Imp_trans. apply Id_list_disj_remove.
apply imp_Id_gen.
Qed.

Lemma der_list_disj_bot : forall l Γ,
  wBIH_prv Γ (list_disj l) -> wBIH_prv Γ (list_disj (remove eq_dec_form ⊥ l)).
Proof.
induction l ; cbn ; intros ; auto.
destruct (eq_dec_form ⊥ a) ; subst.
- apply IHl. apply absorp_Or2 ; auto.
- eapply wMP. eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
  apply wAx ; eapply A3 ; reflexivity. eapply wMP. eapply wMP. apply Imp_trans.
  apply wBIH_Deduction_Theorem. apply IHl. apply wId. right ; apply In_singleton.
  apply wAx ; eapply A4 ; reflexivity. auto.
Qed.

Lemma list_disj_remove_form : forall l Γ A,
  wBIH_prv Γ (list_disj l) -> wBIH_prv Γ (A ∨ list_disj (remove eq_dec_form A l)).
Proof.
intros. pose (remove_disj l A Γ). apply wBIH_Detachment_Theorem in w.
apply wBIH_comp with (Γ':=Γ) in w ; auto. intros. inversion H0 ; subst.
apply wId ; auto. inversion H1 ; subst ; auto.
Qed.

Lemma list_disj_In0 : forall l Γ A,
  List.In A l ->
  wBIH_prv Γ (A --> list_disj l).
Proof.
induction l ; cbn ; intros ; try contradiction.
destruct H ; subst ; cbn in *.
- apply wAx ; eapply A3 ; reflexivity.
- eapply wMP. eapply wMP. apply Imp_trans.
  apply IHl ; auto. apply wAx ; eapply A4 ; reflexivity.
Qed.

Lemma list_disj_In : forall l Γ A,
  List.In A l ->
  wBIH_prv Γ (A ∨ list_disj l) ->
  wBIH_prv Γ (list_disj l).
Proof.
induction l ; cbn ; intros ; try contradiction.
eapply wMP. eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity.
destruct H ; subst.
apply wAx ; eapply A3 ; reflexivity.
eapply wMP. eapply wMP. apply Imp_trans.
apply list_disj_In0 ; auto. exact i. apply wAx ; eapply A4 ; reflexivity.
apply imp_Id_gen. auto.
Qed.

Lemma list_disj_app_distr : forall Γ l0 l1,
  wBIH_prv Γ (list_disj l0 ∨ list_disj l1) ->
  wBIH_prv Γ (list_disj (l0 ++ l1)).
Proof.
intros. eapply wMP. apply list_disj_app0. apply imp_Id_gen. auto.
Qed.

Lemma list_disj_In_prv : forall Γ l0 l1,
  (forall A, List.In A l0 -> List.In A l1) ->
  wBIH_prv Γ (list_disj l0) ->
  wBIH_prv Γ (list_disj l1).
Proof.
intros Γ l0. revert l0 Γ. induction l0 ; cbn ; intros.
- eapply wMP. apply EFQ. auto.
- eapply wMP. eapply wMP. eapply wMP.
  apply wAx ; eapply A5 ; reflexivity.
  apply list_disj_In0 ; auto. apply wBIH_Deduction_Theorem.
  apply IHl0 ; auto. apply wId ; right ; apply In_singleton. auto.
Qed.

Lemma list_disj_nodup : forall Γ l,
  wBIH_prv Γ (list_disj l) ->
  wBIH_prv Γ (list_disj (nodup eq_dec_form l)).
Proof.
intros Γ l. revert Γ. induction l ; cbn ; intros ; auto.
destruct (in_dec eq_dec_form a l).
- apply IHl ; auto. eapply wMP. eapply wMP. eapply wMP.
  apply wAx ; eapply A5 ; reflexivity.
  apply list_disj_In0 ; exact i. apply imp_Id_gen.
  auto.
- cbn. eapply wMP. eapply wMP. eapply wMP.
  apply wAx ; eapply A5 ; reflexivity.
  apply wAx ; eapply A3 ; reflexivity.
  eapply wMP. eapply wMP. apply Imp_trans.
  apply wBIH_Deduction_Theorem. apply IHl. apply wId.
  right ; apply In_singleton.
  apply wAx ; eapply A4 ; reflexivity.
  auto.
Qed.

Lemma forall_list_disj : forall l Γ A,
  wBIH_prv Γ (list_disj l) ->
  (forall B, List.In B l -> wBIH_prv Γ (B --> A)) ->
  wBIH_prv Γ A.
Proof.
induction l ; cbn ; intros ; auto.
- eapply wMP. apply EFQ. auto.
- eapply wMP. eapply wMP. eapply wMP.
  apply wAx ; eapply A5 ; reflexivity.
  apply H0. left ; reflexivity.
  apply wBIH_Deduction_Theorem. apply IHl.
  apply wId. right ; apply In_singleton.
  intros. apply wBIH_monot with Γ. apply H0 ; auto.
  intros C HC ; left ; auto. auto.
Qed.

End list_disj_stuff.





Section list_conj_stuff.

Lemma list_conj_in_list : forall Γ l A,
  List.In A l ->
  wBIH_prv Γ ((list_conj l) --> A).
Proof.
induction l.
- intros. inversion H.
- intros. cbn. inversion H. subst. apply wAx ; eapply A6 ; reflexivity. apply IHl in H0.
  eapply wMP. eapply wMP. apply Imp_trans. apply wAx ; eapply A7 ; reflexivity. auto.
Qed.

Lemma finite_context_list_conj : forall Γ A,
  wBIH_prv Γ A ->
  forall l, (forall A : form, (Γ A -> List.In A l) * (List.In A l -> Γ A)) ->
  wBIH_prv (Singleton _ (list_conj l)) A.
Proof.
intros. apply (wBIH_comp _ _ H (Singleton form (list_conj l))). intros B HB.
eapply wMP. apply list_conj_in_list. apply H0 ; exact HB.
apply wId. apply In_singleton.
Qed.

Lemma der_list_conj_finite_context : forall l (Γ : Ensemble _),
  (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  wBIH_prv Γ (list_conj l).
Proof.
induction l ; intros.
- cbn. apply prv_Top.
- cbn. destruct (In_dec l a).
  + assert (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)).
     intros. split ; intro. apply H in H0. inversion H0. subst. auto. auto.
     apply H. apply in_cons ; auto. pose (IHl Γ H0).
     eapply wMP. eapply wMP. eapply wMP. apply wAx ; eapply A8 ; reflexivity.
     eapply wMP. apply Thm_irrel. apply wId. apply H ; apply in_eq. apply imp_Id_gen. auto. 
  + assert (J1: (forall B : form, ((fun x : form => In form Γ x /\ x <> a) B -> List.In B l) * (List.In B l -> (fun x : form => In form Γ x /\ x <> a) B))).
     intros. split ; intro. destruct H0. apply H in H0. inversion H0. subst. exfalso. apply H1 ; auto. auto.
     split. apply H. apply in_cons ; auto. intro. subst. auto.
     pose (IHl (fun x => In _ Γ x /\ x <> a) J1).
     eapply wMP. eapply wMP. eapply wMP. apply wAx ; eapply A8 ; reflexivity.
     eapply wMP. apply Thm_irrel. apply wId. apply H ; apply in_eq. apply imp_Id_gen.
     apply wBIH_monot with (Γ1:=Γ) in w. apply w. intros C HC.
     inversion HC. auto.
Qed.

Lemma list_conj_finite_context : forall l (Γ : Ensemble _) A,
  (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  wBIH_prv (Singleton _ (list_conj l)) A ->
  wBIH_prv Γ A.
Proof.
intros.
apply wBIH_comp with (Γ:=(Singleton form (list_conj l))) ; auto.
intros. inversion H1 ; subst. apply der_list_conj_finite_context.
intro B ; split ; intro HB ; apply H ; auto.
Qed.

End list_conj_stuff.





Section Bi_Int.

Theorem ctx_dual_residuation_obj : forall Γ A B C,
  (wBIH_prv Γ ((A --< B) --> C) ->
      wBIH_prv Γ (A --> ((B ∨ C)))).
Proof.
intros Γ A B C D. eapply wMP. eapply wMP. apply Imp_trans.
eapply wMP. eapply wMP. apply Imp_trans. apply wAx ; eapply BA1 ; reflexivity.
apply comm_Or_obj. apply monot_Or2. auto.
Qed.

Theorem dual_residuation_obj : forall A B C,
  (wBIH_prv (Empty_set _) ((A --< B) --> C) ->
      wBIH_prv (Empty_set _) (A --> ((B ∨ C)))).
Proof.
intros A B C D. eapply wMP. eapply wMP. apply Imp_trans.
eapply wMP. eapply wMP. apply Imp_trans. apply wAx ; eapply BA1 ; reflexivity.
apply comm_Or_obj. apply monot_Or2. auto.
Qed.

Lemma DN_to_form : forall A Γ, wBIH_prv Γ ((¬ (∞ A)) --> A).
Proof.
intros A Γ. eapply wMP. eapply wMP. apply And_Imp. eapply wMP.
eapply wMP. apply Imp_trans. eapply wMP. eapply wMP.
apply wAx ; eapply A8 ; reflexivity. apply wAx ; eapply A7 ; reflexivity.
apply wAx ; eapply A6 ; reflexivity. eapply wMP. apply Imp_And.
eapply wMP. eapply wMP. apply Imp_trans. apply imp_Id_gen.
eapply wMP. eapply wMP. apply Imp_trans. eapply wMP.
apply Imp_trans. apply imp_Id_gen. eapply wMP.
eapply wMP. apply Imp_trans. apply imp_Id_gen.
apply wAx ; eapply BA4 ; reflexivity. apply prv_Top.
Qed.

Theorem dual_residuation : forall A B C,
  wBIH_prv (Empty_set _) ((A --< B) --> C) <-> wBIH_prv (Empty_set _) (A --> ((B ∨ C))).
Proof.
intros A B C. split.
- intro D. eapply wMP. eapply wMP. apply Imp_trans.
  eapply wMP. eapply wMP. apply Imp_trans.
  apply wAx ; eapply BA1 ; reflexivity. apply comm_Or_obj.
  apply monot_Or2 ; auto.
- intro D. eapply wMP. eapply wMP. apply Imp_trans.
  eapply wMP. eapply wMP. apply Imp_trans.
  apply wAx ; eapply BA1 ; reflexivity. apply monotL_Or.
  apply wAx ; eapply BA3 ; reflexivity.
  eapply wMP. eapply wMP. apply Imp_trans. apply monotL_Or.
  eapply wMP. eapply wMP. apply Imp_trans.
  eapply wMP. eapply wMP. apply wAx ; eapply A8 ; reflexivity.
  apply wAx ; eapply BA2 ; reflexivity. eapply wMP. apply Thm_irrel.
  apply wDN. exact D. apply Contr_Bot.
  eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
  apply imp_Id_gen. apply wAx ; eapply A9 ; reflexivity.
Qed.

Lemma AThm_irrel : forall A B Γ, wBIH_prv Γ ((A --< B) --> A).
Proof.
intros A B Γ. apply wBIH_monot with (Γ:= Empty_set _).
apply dual_residuation. apply wAx ; eapply A4 ; reflexivity.
intros C HC ; inversion HC.
Qed.

Theorem dual_residuation_gen : forall A B C,
  wpair_der (Empty_set _) (Singleton _ ((A --< B) --> C))  <-> wpair_der (Empty_set _) (Singleton _ (A --> ((B ∨ C)))).
Proof.
intros A B C. split.
- intro. exists [(A --> (B ∨ C))]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. cbn. apply In_singleton. inversion H1.
  * destruct H as (l & H0 & H1 & H2). cbn. eapply wMP. apply wAx ; eapply A3 ; reflexivity.
    apply dual_residuation. destruct l ; cbn in *.
    + eapply wMP. apply wAx ; eapply A9 ; reflexivity. auto.
    + destruct l ; cbn in *. apply absorp_Or1 in H2. assert (Singleton form ((A --< B) --> C) f).
       apply H1 ; auto. inversion H ; subst ; auto. exfalso. inversion H0 ; subst.
       apply H4. assert (Singleton form ((A --< B) --> C) f). apply H1 ; auto. inversion H ; subst.
       assert (Singleton form ((A --< B) --> C) f0). apply H1 ; auto. inversion H3 ; subst. apply in_eq.
- intro. exists  [((A --< B) --> C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. cbn. apply In_singleton. inversion H1.
  * destruct H as (l & H0 & H1 & H2). cbn. eapply wMP. apply wAx ; eapply A3 ; reflexivity.
    apply dual_residuation. destruct l ; cbn in *.
    + eapply wMP. apply wAx ; eapply A9 ; reflexivity. auto.
    + destruct l ; cbn in *. apply absorp_Or1 in H2. assert (Singleton form (A --> B ∨ C) f).
       apply H1 ; auto. inversion H ; subst ; auto. exfalso. inversion H0 ; subst.
       apply H4. assert (Singleton form (A --> B ∨ C) f). apply H1 ; auto. inversion H ; subst.
       assert (Singleton form (A --> B ∨ C) f0). apply H1 ; auto. inversion H3 ; subst. apply in_eq.
Qed.

Lemma BiLEM : forall A Γ, wBIH_prv Γ (A ∨ (∞ A)).
Proof.
intros. apply wBIH_monot with (Γ:=Empty_set _).
eapply wMP. rewrite <- dual_residuation. apply imp_Id_gen.
apply prv_Top. intros B HB ; inversion HB.
Qed.

Theorem wBIH_Dual_Detachment_Theorem : forall A B Δ,
           wBIH_prv (Singleton _ (A --< B)) (list_disj Δ) ->
           wBIH_prv (Singleton _ A) (B ∨ (list_disj Δ)).
Proof.
intros A B Δ D.
apply wBIH_monot with (Γ1:=Union _ (Empty_set form) (Singleton _ (A --< B))) in D.
apply wBIH_Deduction_Theorem in D. apply dual_residuation in D.
apply wBIH_Detachment_Theorem in D. apply (wBIH_monot _ _ D).
intros C HC ; inversion HC ; [ inversion H | auto].
intros C HC ; right ; auto.
Qed.

Theorem wBIH_Dual_Deduction_Theorem : forall A B Δ,
           wBIH_prv (Singleton _ A) (B ∨ (list_disj Δ)) ->
           wBIH_prv (Singleton _ (A --< B)) (list_disj Δ).
Proof.
intros A B Δ D.
apply wBIH_monot with (Γ1:=Union _ (Empty_set form) (Singleton _ A)) in D.
apply wBIH_Deduction_Theorem in D. apply dual_residuation in D.
apply wBIH_Detachment_Theorem in D. apply (wBIH_monot _ _ D).
intros C HC ; inversion HC ; [ inversion H | auto].
intros C HC ; right ; auto.
Qed.

Theorem gen_wBIH_Dual_Detachment_Theorem : forall A B Δ,
  wpair_der (Singleton _ (A --< B)) Δ ->
      wpair_der (Singleton _ A) (Union _ (Singleton _ B) Δ).
Proof.
intros A B Δ wpair. destruct wpair. destruct H. destruct H0. cbn in H0. cbn in H1.
exists (B :: (remove eq_dec_form B x)). repeat split.
apply NoDup_cons. apply remove_In. apply NoDup_remove. assumption.
intros. inversion H2 ; subst ; cbn ; auto. left. apply In_singleton.
right. apply H0. apply In_remove with (B:=B). assumption.
cbn. eapply wMP. eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
apply wAx ; eapply A3 ; reflexivity. apply remove_disj.
apply wBIH_Dual_Detachment_Theorem ; auto.
Qed.

Theorem gen_wBIH_Dual_Deduction_Theorem : forall A B Δ,
  wpair_der (Singleton _ A) (Union _ (Singleton _ B) Δ) ->
      wpair_der (Singleton _ (A --< B)) Δ.
Proof.
intros A B Δ wpair. destruct wpair. destruct H. destruct H0. cbn in H0. cbn in H1.
exists (remove eq_dec_form B x). repeat split.
apply NoDup_remove. assumption.
intros. cbn. pose (H0 A0). pose (In_remove _ _ _ H2). apply u in i.
destruct i. inversion H3. subst. exfalso. pose (remove_In eq_dec_form x x0).
apply n. assumption. assumption.
apply wBIH_Dual_Deduction_Theorem. eapply wMP. apply remove_disj. auto.
Qed.

Theorem dual_MP : forall A B Δ,
  wpair_der (Singleton _ (A --< B)) Δ ->
  wpair_der (Singleton _ B) Δ ->
      wpair_der (Singleton _ A) Δ.
Proof.
intros.
destruct H as (x & K0 & K1 & K2).
destruct H0 as (x0 & K3 & K4 & K5).
exists (x ++ remove_list x x0). repeat split.
apply add_remove_list_preserve_NoDup ; auto.
intros C HC. destruct (in_app_or _ _ _ HC) ; auto.
apply In_remove_list_In_list in H ; auto.
assert (wBIH_prv (Singleton form (A --< B)) (list_disj (x ++ remove_list x x0))).
apply wBIH_monot with (Γ:=(Union _ (Empty_set _) (Singleton form (A --< B)))).
apply wBIH_Detachment_Theorem. apply der_list_disj_remove1.
apply wBIH_Deduction_Theorem. apply wBIH_monot with (Γ:=Singleton form (A --< B)) ; auto.
intros C HC ; inversion HC ; right ; apply In_singleton.
intros C HC ; inversion HC ; [inversion H | auto].
assert (wBIH_prv (Singleton form B) (list_disj (x ++ remove_list x x0))).
apply wBIH_monot with (Γ:=(Union _ (Empty_set _) (Singleton form B))).
apply wBIH_Detachment_Theorem. apply der_list_disj_remove2.
apply wBIH_Deduction_Theorem. apply wBIH_monot with (Γ:=Singleton form B) ; auto.
intros C HC ; inversion HC ; right ; apply In_singleton.
intros C HC ; inversion HC ; [inversion H0 | auto].
apply wBIH_monot with (Γ:=(Union _ (Empty_set _) (Singleton form A))).
apply wBIH_Detachment_Theorem.
eapply wMP. eapply wMP. apply Imp_trans. apply wAx ; eapply BA1 ; reflexivity.
eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
apply wBIH_Deduction_Theorem. apply wBIH_monot with (Γ:=Singleton form B) ; auto.
intros C HC ; inversion HC ; right ; apply In_singleton.
apply wBIH_Deduction_Theorem. apply wBIH_monot with (Γ:=Singleton form (A --< B)) ; auto.
intros C HC ; inversion HC ; right ; apply In_singleton.
intros C HC ; inversion HC ; [inversion H1 | auto].
Qed.

Lemma monoR_Excl : forall A B C,
  (wBIH_prv (Empty_set _) (A -->  B)) ->
  (wBIH_prv (Empty_set _) ((A --< C) -->  (B --< C))).
Proof.
intros. apply dual_residuation.
eapply wMP. eapply wMP. apply Imp_trans. exact H.
apply wAx ; eapply BA1 ; reflexivity.
Qed.

Lemma monoL_Excl : forall A B C,
  (wBIH_prv (Empty_set _) (A -->  B)) ->
  (wBIH_prv (Empty_set _) ((C --< B) -->  (C --< A))).
Proof.
intros. apply dual_residuation.
eapply wMP. eapply wMP. apply Imp_trans.
apply wAx ; eapply BA1 ; reflexivity.
eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
eapply wMP. eapply wMP. apply Imp_trans. exact H.
apply wAx ; eapply A3 ; reflexivity.
apply wAx ; eapply A4 ; reflexivity.
Qed.

End Bi_Int.

(* Having Cut is quite convenient. *)

Lemma Or_imp_assoc : forall A B C D Γ,
  wBIH_prv Γ (A --> ((B ∨ C) ∨ D)) ->
  wBIH_prv Γ (A --> (B ∨ (C ∨ D))).
Proof.
intros. eapply wMP. eapply wMP. apply Imp_trans. exact H.
eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
eapply wMP. eapply wMP. apply wAx ; eapply A5 ; reflexivity.
apply wAx ; eapply A3 ; reflexivity. eapply wMP. eapply wMP.
apply Imp_trans. apply wAx ; eapply A3 ; reflexivity.
apply wAx ; eapply A4 ; reflexivity. eapply wMP.
eapply wMP. apply Imp_trans. apply wAx ; eapply A4 ; reflexivity.
apply wAx ; eapply A4 ; reflexivity.
Qed.

Lemma Cut : forall (Γ Δ: @Ensemble (form)) A,
        wpair_der (Union _ Γ (Singleton _ A)) Δ  ->
        wpair_der Γ (Union _ Δ (Singleton _ A))  ->
        wpair_der Γ Δ.
Proof.
intros.
destruct H. destruct H0. destruct H. destruct H1. destruct H0. destruct H3.
simpl in H2. simpl in H4. simpl in H3. simpl in H1.
exists ((remove eq_dec_form A x0) ++ (remove_list (remove eq_dec_form A x0) x)). repeat split.
apply add_remove_list_preserve_NoDup ; auto.
apply NoDup_remove ; auto. simpl. intros. apply in_app_or in H5. destruct H5.
apply in_remove in H5. destruct H5. apply H3 in H5. inversion H5 ; auto. subst.
inversion H7 ; subst ; exfalso ; auto. apply In_remove_list_In_list in H5.
apply H1 in H5. auto. simpl.
apply wBIH_Deduction_Theorem in H2.
pose (Id_list_disj_remove Γ (remove eq_dec_form A x0) x).
pose (list_disj_remove_form _ _ A H4).
assert (J1: wBIH_prv Γ (list_disj (remove eq_dec_form A x0) --> list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))).
apply Id_list_disj.
eapply wMP. 2: exact w0.
eapply wMP. 2: exact J1.
eapply wMP. apply wAx ; eapply A5 ; reflexivity.
eapply wMP. 2: exact w.
eapply wMP. apply Imp_trans. auto.
Qed.


End properties.


Section connect_to_s.

Lemma Contrapositive : forall A B Γ ,
  wBIH_prv Γ (A --> B) ->
  wBIH_prv Γ (¬ B --> ¬ A).
Proof.
intros. repeat apply wBIH_Deduction_Theorem.
eapply wMP. apply wId ; left ; right ; split.
eapply wMP. apply (wBIH_monot _ _ H) ; auto.
intros C HC ; left ; left ; auto.
apply wId ; right ; split.
Qed.

Lemma T_for_DN : forall A n m Γ , (le m n) -> wBIH_prv Γ ((DN_form n A) -->  (DN_form m A)).
Proof.
intro A. induction n.
- intros. assert (m = 0). lia. rewrite H0. simpl. apply imp_Id_gen.
- intros. destruct (Nat.eq_dec m (S n)).
  * subst. apply imp_Id_gen.
  * assert (m <= n). lia. pose (IHn m Γ  H0).
    eapply wMP. eapply wMP. apply Imp_trans. apply DN_to_form. auto.
Qed.

Lemma Or_Neg : forall A B C Γ ,
  (wBIH_prv Γ (A --> (Or B C))) ->
  (wBIH_prv Γ ((And (¬ B) A) -->  C)).
Proof.
intros.
eapply wMP. eapply wMP. apply Imp_trans.
eapply wMP. eapply wMP.
apply wAx ; eapply A8 ; reflexivity.
apply wAx ; eapply A6 ; reflexivity.
eapply wMP. eapply wMP. apply Imp_trans.
apply wAx ; eapply A7 ; reflexivity. exact H.
eapply wMP. eapply wMP. apply Imp_trans.
eapply wMP. eapply wMP.
apply wAx ; eapply A8 ; reflexivity.
apply wAx ; eapply A7 ; reflexivity.
apply wAx ; eapply A6 ; reflexivity.
apply wBIH_Deduction_Theorem.
eapply wMP. eapply wMP. eapply wMP.
apply wAx ; eapply A5 ; reflexivity.
2: apply imp_Id_gen.
eapply wMP. eapply wMP. apply Imp_trans.
eapply wMP.
eapply wAx ; eapply A7 ; reflexivity. apply wId. right ; split.
apply EFQ.
eapply wMP.
eapply wAx ; eapply A6 ; reflexivity. apply wId. right ; split.
Qed.

Lemma wClaim1 : forall A B Γ ,
    wBIH_prv Γ ((¬ (A --< B)) -->  ((∞ B) --> (∞ A))).
Proof.
intros A B Γ .
apply wBIH_monot with (Empty_set _).
- eapply wMP. apply And_Imp.
  eapply wMP. eapply wMP. apply Imp_trans.
apply Or_Neg. apply dual_residuation.
apply Or_imp_assoc. apply dual_residuation. apply imp_Id_gen.
apply monoL_Excl. apply wAx ; eapply BA1 ; reflexivity.
- intros C HC ; inversion HC.
Qed.

Lemma DN_dist_imp : forall A B Γ ,
    wBIH_prv Γ ( (¬ ∞ (A -->  B)) -->  ((¬ ∞ A) -->  (¬ ∞ B))).
Proof.
intros A B Γ .
eapply wMP. eapply wMP. apply Imp_trans.
eapply wMP. eapply wMP. apply Imp_trans.
apply Contrapositive.
apply wAx ; eapply BA2 ; reflexivity.
 apply wClaim1.
apply wBIH_Deduction_Theorem. apply Contrapositive.
apply wId ; right ; split.
Qed.

Lemma DN_form_dist_imp : forall n A B,
    wBIH_prv (Empty_set _) ( (DN_form n (A --> B)) -->  ((DN_form n A) -->  (DN_form n B))).
Proof.
induction n ; cbn ; intros ; auto.
- apply imp_Id_gen.
- eapply meta_Imp_trans.
  + eapply wMP.
    * apply DN_dist_imp.
    * apply wDN. apply IHn.
  + apply DN_dist_imp.
Qed.

Lemma DN_form_rule : forall n A,
    wBIH_prv (Empty_set _) A -> 
    wBIH_prv (Empty_set _) (DN_form n A).
Proof.
induction n ; cbn ; intros ; auto. apply wDN ; auto.
Qed.

End connect_to_s.