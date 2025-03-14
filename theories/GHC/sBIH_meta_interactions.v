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

Lemma sThm_irrel : forall A B Γ, sBIH_prv Γ (A --> (B --> A)).
Proof.
intros. apply sBIH_extens_wBIH. apply Thm_irrel.
Qed.

Lemma simp_Id_gen : forall A Γ, sBIH_prv Γ (A --> A).
Proof.
intros. apply sBIH_extens_wBIH. apply imp_Id_gen.
Qed.

Lemma scomm_And_obj : forall A B Γ, (sBIH_prv Γ (And A B --> And B A)).
Proof.
intros. apply sBIH_extens_wBIH. apply comm_And_obj.
Qed.

Lemma sassoc_And_obj : forall A B C Γ, sBIH_prv Γ (A ∧ B ∧ C --> (A ∧ B) ∧ C) /\ 
                                      sBIH_prv Γ ((A ∧ B) ∧ C --> A ∧ B ∧ C).
Proof.
intros A B C Γ ; split ; apply sBIH_extens_wBIH ; apply assoc_And_obj.
Qed.

Lemma sContr_Bot : forall A Γ, sBIH_prv Γ (And A (¬ A) --> (Bot)).
Proof.
intros. apply sBIH_extens_wBIH. apply Contr_Bot.
Qed.

Lemma sEFQ : forall A Γ, sBIH_prv Γ ((Bot) --> A).
Proof.
intros. apply sBIH_extens_wBIH. apply EFQ.
Qed.

Lemma sprv_Top : forall Γ , sBIH_prv Γ ⊤.
Proof.
intros. apply sBIH_extens_wBIH. apply prv_Top.
Qed.

Lemma scomm_Or_obj : forall A B Γ, (sBIH_prv Γ (Or A B --> Or B A)).
Proof.
intros. apply sBIH_extens_wBIH. apply comm_Or_obj.
Qed.

Lemma sImp_trans : forall A B C Γ, sBIH_prv Γ ((A --> B) -->  (B --> C) --> (A --> C)).
Proof.
intros. apply sBIH_extens_wBIH. apply Imp_trans.
Qed.

Lemma meta_sImp_trans : forall A B C Γ, sBIH_prv Γ (A --> B) -> sBIH_prv Γ (B --> C) ->
                sBIH_prv Γ (A --> C).
Proof.
intros A B C Γ H H0. eapply sMP. 
- eapply sMP.
  + eapply sImp_trans.
  + exact H.
- auto.
Qed.

Lemma smonotR_Or : forall A B Γ ,
    sBIH_prv Γ (A -->  B) ->
    forall C, sBIH_prv Γ ((A ∨ C) -->  (B ∨ C)).
Proof.
intros A B Γ D C. eapply sMP. eapply sMP.
apply sAx ; eapply A5 ; reflexivity.
eapply sMP. eapply sMP. apply sImp_trans. exact D.
apply sAx ; eapply A3 ; reflexivity.
apply sAx ; eapply A4 ; reflexivity.
Qed.

Lemma smonotL_Or : forall A B Γ,
    sBIH_prv Γ (A -->  B) ->
    forall C, sBIH_prv Γ ((C ∨ A) -->  (C ∨ B)).
Proof.
intros A B Γ D C. eapply sMP. eapply sMP.
apply sAx ; eapply A5 ; reflexivity.
apply sAx ; eapply A3 ; reflexivity.
eapply sMP. eapply sMP. apply sImp_trans. exact D.
apply sAx ; eapply A4 ; reflexivity.
Qed.

Lemma scomm_Or : forall A B Γ,
    (sBIH_prv Γ (Or A B)) ->
    (sBIH_prv Γ (Or B A)).
Proof.
intros A B Γ D. eapply sMP. apply scomm_Or_obj. auto.
Qed.

Lemma monot_Or2 : forall A B Γ, sBIH_prv Γ (A -->  B) ->
    forall C, sBIH_prv Γ ((A ∨ C) -->  (C ∨ B)).
Proof.
intros A B Γ D C.
eapply sMP. eapply sMP.
apply sAx ; eapply A5 ; reflexivity.
eapply sMP. eapply sMP. apply sImp_trans. exact D.
apply sAx ; eapply A4 ; reflexivity.
apply sAx ; eapply A3 ; reflexivity.
Qed.

Lemma sabsorp_Or1 : forall A Γ ,
    sBIH_prv Γ (A ∨ ⊥) ->
    sBIH_prv Γ A.
Proof.
intros A Γ D. eapply sMP. eapply sMP. eapply sMP.
apply sAx ; eapply A5 ; reflexivity.
apply simp_Id_gen. apply sEFQ. auto.
Qed.

Lemma sImp_And : forall A B C Γ, sBIH_prv Γ ((A -->  (B -->  C)) --> ((A ∧ B) -->  C)).
Proof.
intros. apply sBIH_extens_wBIH. apply Imp_And.
Qed.

Lemma sAnd_Imp : forall A B C Γ, sBIH_prv Γ (((A ∧ B) -->  C) --> (A --> (B -->  C))).
Proof.
intros. apply sBIH_extens_wBIH. apply And_Imp.
Qed.

Theorem sBIH_Detachment_Theorem : forall A B Γ,
           sBIH_prv Γ (A --> B) ->
           sBIH_prv  (Union _ Γ  (Singleton _ (A))) B.
Proof.
intros A B Γ D. eapply sMP. apply (sBIH_monot Γ (A --> B)) ; auto.
intros C HC. apply Union_introl ; auto.
apply sId. apply Union_intror. apply In_singleton.
Qed.

Theorem gen_sBIH_Detachment_Theorem : forall A B Γ,
  spair_der Γ (Singleton _ (A --> B)) ->
      spair_der (Union form Γ (Singleton form A))  (Singleton _ B).
Proof.
intros A B Γ spair. unfold spair_der. exists [B]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. cbn. apply In_singleton. inversion H0.
cbn. eapply sMP. apply sAx ; eapply A3 ; reflexivity.
destruct spair as (l & Hl0 & Hl1 & Hl2). destruct l ; cbn in *.
eapply sMP. apply sEFQ. apply (sBIH_monot _ _ Hl2).
intros C HC ; left ; auto.
destruct l. cbn in *. assert (Singleton form (A --> B) f). apply Hl1 ; auto.
inversion H ; subst. apply sabsorp_Or1 in Hl2. apply sBIH_Detachment_Theorem in Hl2 ; auto.
exfalso. cbn in *. assert (Singleton form (A --> B) f). apply Hl1 ; auto.
assert (Singleton form (A --> B) f0). apply Hl1 ; auto. inversion H ; subst.
inversion H0 ; subst. inversion Hl0 ; subst. apply H3 ; apply in_eq.
Qed.


Lemma sOr_Neg : forall A B C Γ,
  (sBIH_prv Γ (A --> (Or B C))) ->
  (sBIH_prv Γ ((And (¬ B) A) --> C)).
Proof.
intros.
eapply sMP. eapply sMP. apply sImp_trans.
eapply sMP. eapply sMP.
apply sAx ; eapply A8 ; reflexivity.
apply sAx ; eapply A6 ; reflexivity.
eapply sMP. eapply sMP. apply sImp_trans.
apply sAx ; eapply A7 ; reflexivity. exact H.
eapply sMP. eapply sMP. apply sImp_trans.
eapply sMP. eapply sMP.
apply sAx ; eapply A8 ; reflexivity.
apply sAx ; eapply A7 ; reflexivity.
apply sAx ; eapply A6 ; reflexivity.
eapply sMP. apply sImp_And.
eapply sMP. eapply sMP.
apply sAx ; eapply A5 ; reflexivity.
eapply sMP. apply sAnd_Imp.
eapply sMP. eapply sMP. apply sImp_trans.
apply sContr_Bot. apply sEFQ. apply sThm_irrel.
Qed.

Lemma sOr_imp_assoc : forall A B C D Γ,
  sBIH_prv Γ (A --> ((B ∨ C) ∨ D)) ->
  sBIH_prv Γ (A --> (B ∨ (C ∨ D))).
Proof.
intros. eapply sMP. eapply sMP. apply sImp_trans. exact H.
eapply sMP. eapply sMP. apply sAx ; eapply A5 ; reflexivity.
eapply sMP. eapply sMP. apply sAx ; eapply A5 ; reflexivity.
apply sAx ; eapply A3 ; reflexivity. eapply sMP. eapply sMP.
apply sImp_trans. apply sAx ; eapply A3 ; reflexivity.
apply sAx ; eapply A4 ; reflexivity. eapply sMP.
eapply sMP. apply sImp_trans. apply sAx ; eapply A4 ; reflexivity.
apply sAx ; eapply A4 ; reflexivity.
Qed.


Section BiInt.

Theorem sdual_residuation : forall A B C Γ,
  sBIH_prv Γ ((A --< B) --> C) <-> sBIH_prv Γ (A --> (B ∨ C)).
Proof.
intros A B C Γ. split.
- intro D. eapply sMP. eapply sMP. apply sImp_trans.
  eapply sMP. eapply sMP. apply sImp_trans.
  apply sAx ; eapply BA1 ; reflexivity. apply scomm_Or_obj.
  apply monot_Or2 ; auto.
- intro D. eapply sMP. eapply sMP. apply sImp_trans.
  eapply sMP. eapply sMP. apply sImp_trans.
  apply sAx ; eapply BA1 ; reflexivity. apply smonotL_Or.
  apply sAx ; eapply BA3 ; reflexivity.
  eapply sMP. eapply sMP. apply sImp_trans. apply smonotL_Or.
  eapply sMP. eapply sMP. apply sImp_trans.
  eapply sMP. eapply sMP. apply sAx ; eapply A8 ; reflexivity.
  apply sAx ; eapply BA2 ; reflexivity. eapply sMP. apply sThm_irrel.
  apply sDN. exact D. apply sContr_Bot.
  eapply sMP. eapply sMP. apply sAx ; eapply A5 ; reflexivity.
  apply simp_Id_gen. apply sAx ; eapply A9 ; reflexivity.
Qed.

Theorem spair_dual_residuation_gen : forall A B C Γ,
  spair_der Γ (Singleton _ ((A --< B) --> C)) <-> spair_der Γ (Singleton _ (A --> (B ∨ C))).
Proof.
intros A B C Γ. split.
- intro. exists [(A --> Or B C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0 ; subst. split. inversion H1.
  * cbn. eapply sMP. apply sAx ; eapply A3 ; reflexivity.
    destruct H as (l & Hl0 & Hl1 & Hl2). destruct l. cbn in Hl2. eapply sMP. apply sEFQ. auto.
    destruct l. cbn in Hl2. apply sdual_residuation. eapply sMP. 2: exact Hl2.
    eapply sMP. eapply sMP. apply sAx ; eapply A5 ; reflexivity.
    destruct Hl1 with f ; cbn ; auto. apply simp_Id_gen. apply sEFQ.
    exfalso. destruct Hl1 with f ; cbn ; auto. destruct Hl1 with f0 ; cbn ; auto.
    inversion Hl0 ; subst. apply H1 ; cbn ; auto.
- intro. exists [(Excl A B --> C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0 ; subst. split. inversion H1.
  * cbn. eapply sMP. apply sAx ; eapply A3 ; reflexivity.
    destruct H as (l & Hl0 & Hl1 & Hl2). destruct l. cbn in Hl2. eapply sMP. apply sEFQ. auto.
    destruct l. cbn in Hl2. apply sdual_residuation. eapply sMP. 2: exact Hl2.
    eapply sMP. eapply sMP. apply sAx ; eapply A5 ; reflexivity.
    destruct Hl1 with f ; cbn ; auto. apply simp_Id_gen. apply sEFQ.
    exfalso. destruct Hl1 with f ; cbn ; auto. destruct Hl1 with f0 ; cbn ; auto.
    inversion Hl0 ; subst. apply H1 ; cbn ; auto.
Qed.

Lemma sDN_to_form : forall A Γ, (sBIH_prv Γ (¬ (∞ A)--> A)).
Proof.
intros A Γ. apply sBIH_extens_wBIH. apply DN_to_form.
Qed.

Lemma sT_for_DN : forall A n m Γ, (le m n) -> (sBIH_prv Γ ((DN_form n A) --> (DN_form m A))).
Proof.
intros. apply sBIH_extens_wBIH. apply T_for_DN. assumption.
Qed.

Lemma smonoR_Excl : forall A B C Γ,
  sBIH_prv Γ (A -->  B) ->
  sBIH_prv Γ ((A --< C) -->  (B --< C)).
Proof.
intros. apply sdual_residuation.
eapply sMP. eapply sMP. apply sImp_trans. exact H.
apply sAx ; eapply BA1 ; reflexivity.
Qed.

Lemma smonoL_Excl : forall A B C Γ,
  sBIH_prv Γ (A -->  B) ->
  sBIH_prv Γ ((C --< B) -->  (C --< A)).
Proof.
intros. apply sdual_residuation.
eapply sMP. eapply sMP. apply sImp_trans.
apply sAx ; eapply BA1 ; reflexivity.
eapply sMP. eapply sMP. apply sAx ; eapply A5 ; reflexivity.
eapply sMP. eapply sMP. apply sImp_trans. exact H.
apply sAx ; eapply A3 ; reflexivity.
apply sAx ; eapply A4 ; reflexivity.
Qed.

Lemma sClaim1 : forall A B Γ,
    (sBIH_prv Γ ((¬ (A --< B)) --> ((∞ B) --> (∞ A)))).
Proof.
intros A B Γ. apply sBIH_extens_wBIH. apply wClaim1.
Qed.

Lemma sDN_dist_imp : forall A B Γ,
    (sBIH_prv Γ ((¬ (∞ (A --> B))) --> ((¬ (∞ A)) --> (¬ (∞ B))))).
Proof.
intros A B Γ. apply sBIH_extens_wBIH. apply DN_dist_imp.
Qed.

Lemma sDN_form_dist_imp : forall n A B Γ,
    sBIH_prv Γ ( (DN_form n (A --> B)) -->  ((DN_form n A) -->  (DN_form n B))).
Proof.
intros n A B Γ. eapply sBIH_monot. apply sBIH_extens_wBIH. apply DN_form_dist_imp.
intros C HC ; inversion HC.
Qed.

Theorem sBIH_Deduction_Theorem : forall Γ A B,
           sBIH_prv (Union _ Γ  (Singleton _ (A))) B ->
           exists n, sBIH_prv Γ ((DN_form n A) -->  B).
Proof.
intros. remember (Union form Γ (Singleton form A)) as L.
revert L B H A Γ HeqL.
intros L B D. induction D ; intros C Γ0 id ; subst.
(* sId *)
- inversion H ; subst ; cbn.
  + exists 0 ; cbn. eapply sMP. apply sThm_irrel. apply sId ; auto.
  + inversion H0 ; subst. exists 0 ; cbn. apply simp_Id_gen.
(* sAx *)
- exists 0 ; cbn. eapply sMP. apply sThm_irrel. apply sAx ; assumption.
(* sMP *)
- destruct (IHD1 C Γ0) ; auto. destruct (IHD2 C Γ0) ; auto. exists (x + x0).
  eapply sMP. eapply sMP. apply sImp_trans.
  eapply sMP. eapply sMP. apply sAx ; eapply A8 ; reflexivity.
  3: eapply sMP. 3: apply sImp_And. 3: eapply simp_Id_gen.
  eapply sMP. eapply sMP. apply sImp_trans.
  2: exact H. apply sT_for_DN. lia.
  eapply sMP. eapply sMP. apply sImp_trans.
  2: exact H0. apply sT_for_DN. lia.
(* sDN *)
- destruct (IHD C Γ0) ; auto. exists (S x). cbn.
  eapply sMP. apply sDN_dist_imp. apply sDN ; auto.
Qed.

Theorem gen_sBIH_Deduction_Theorem : forall A B Γ,
  spair_der (Union _ Γ (Singleton _ A)) (Singleton _ B) ->
      (exists n, spair_der Γ (Singleton _ ((DN_form n A) --> B))).
Proof.
intros A B Γ spair. unfold spair_der. simpl. destruct spair.
destruct H. destruct H0. simpl in H1. simpl in H0. destruct x.
- simpl in H1.
  apply sBIH_Deduction_Theorem in H1. destruct H1. exists x. exists [DN_form x A --> B] ; cbn.
  repeat split.
  * apply NoDup_cons ; auto.
  * intros C HC ; destruct HC ; subst ; auto. split. contradiction.
  * eapply sMP. apply sAx ; eapply A3 ; reflexivity.
    eapply sMP. eapply sMP. apply sImp_trans. exact H1. apply sEFQ.
- destruct x ; cbn in *.
  -- apply sabsorp_Or1 in H1.
  apply sBIH_Deduction_Theorem in H1. destruct H1. exists x. exists [DN_form x A --> B] ; cbn.
  repeat split.
  * apply NoDup_cons ; auto. apply NoDup_nil.
  * intros C HC ; destruct HC ; subst ; auto. split. contradiction.
  * eapply sMP. apply sAx ; eapply A3 ; reflexivity.
    eapply sMP. eapply sMP. apply sImp_trans. exact H1. destruct (H0 f) ; auto.
    apply simp_Id_gen.
  -- exfalso. destruct (H0 f) ; auto. destruct (H0 f0) ; auto. inversion H ; subst. apply H4 ; cbn ; auto.
Qed.

Lemma Closure_DN_strong : forall Γ A, sBIH_prv Γ A -> forall n, sBIH_prv Γ (DN_form n A).
Proof.
intros. induction n.
- simpl. auto.
- simpl. apply sDN. auto. 
Qed.

Theorem gen_sBIH_Double_Negated_Detachment_Theorem : forall A B Γ,
  (exists n, spair_der Γ (Singleton _ ((DN_form n A) --> B))) ->
      spair_der (Union _ Γ (Singleton _ A)) (Singleton _ B).
Proof.
intros A B Γ spair. destruct spair as (n & (l & H0 & H1 & H2)).
destruct l ; cbn in *.
- exists [] ; cbn ; repeat split ; auto.
  + intros ; contradiction.
  + apply (sBIH_monot _ _ H2). intros C HC ; left ; auto.
- destruct l ; cbn in *.
  + apply sabsorp_Or1 in H2. exists [B]. repeat split ; auto.
    * apply NoDup_cons ; auto. apply NoDup_nil.
    * intros C HC ; inversion HC ; subst. split. inversion H.
    * cbn. eapply sMP. apply sAx ; eapply A3 ; reflexivity.
      destruct (H1 f) ; auto.
      eapply sMP. apply (sBIH_monot _ _ H2). intros C HC ; left ; auto.
      apply Closure_DN_strong. apply sId ; right ; split.
  + exfalso. destruct (H1 f) ; auto. destruct (H1 f0) ; auto.
     inversion H0 ; subst. apply H4 ; cbn ; auto.
Qed.

End BiInt.









