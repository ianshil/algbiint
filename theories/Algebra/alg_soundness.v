Require Import List.

Require Import Syntax.
Require Import Bi_Heyting_Algebras.
Require Import algebraic_semantic.
Require Import BIH_export.

Section Soundness.

(* Axioms are all higher than one in any algebras with any interpretation. *)

Lemma Axioms_one : forall ϕ, Axioms ϕ -> forall A amap, aleq A one (interp A amap ϕ).
Proof.
intros ϕ Ax A amap.
inversion Ax ; subst ; cbn.
- apply alg_A1.
- apply alg_A2.
- apply alg_A3.
- apply alg_A4.
- apply alg_A5.
- apply alg_A6.
- apply alg_A7.
- apply alg_A8.
- apply alg_A9.
- apply alg_A10.
- apply alg_BA1.
- apply alg_BA2.
- apply alg_BA3.
- apply alg_BA4.
Qed.

(* We can then show that wBIH is sound with respect to the partial order
   semantic consequence. *)

   Theorem algord_soundness_wBIH Γ ϕ : wBIH_prv Γ ϕ -> alg_ordconseq Γ ϕ.
Proof.
intro. induction H ; intros BH amap a J.
- apply J ; auto.
- apply aleq_trans with one ; [ apply high_one | apply Axioms_one ; auto].
- pose (IHwBIH_prv1 _ _ _ J). cbn in a0 ; apply ord_resid in a0.
  apply aleq_trans with (meet a (interp BH amap A)) ; auto.
  apply glb ; [ apply aleq_refl | apply IHwBIH_prv2 ; auto].
- assert (forall γ : form, Ensembles.Empty_set _ γ -> aleq BH one (interp BH amap γ)).
  { intros C HC ; inversion HC. }
  apply IHwBIH_prv in H0. 
  eapply aleq_trans ; [ apply high_one | ].
  apply ord_resid. rewrite mcomm ; rewrite greatest.
  apply ord_dresid. rewrite lowest ; auto.
Qed.

Theorem algtd_soundness_wBIH Γ ϕ : wBIH_prv Γ ϕ -> alg_tdconseq Γ ϕ.
Proof.
intro. induction H.
- exists (fun x => x = A). repeat split ; intros ; subst ; auto.
  exists (cons A nil). intros ; split ; intro ; subst ; auto.
  + inversion H0 ; subst ; auto. inversion H1.
  + cbn ; auto.
- exists (fun x => False). repeat split ; intros ; try contradiction ; auto.
  + exists nil. intros ; split ; intro ; subst ; auto.
  + apply aleq_trans with one ; [ apply high_one | apply Axioms_one ; auto].
- destruct IHwBIH_prv1 as (Δ1 & H1 & (l1 & H2) & H3).
  destruct IHwBIH_prv2 as (Δ2 & H4 & (l2 & H5) & H6).
  exists (fun x => Δ1 x \/ Δ2 x). repeat split ; intros ; auto.
  + destruct H7 ; auto.
  + exists (l1 ++ l2) . intro γ ; split ; intro.
    * apply in_app_or in H7. destruct H7 ; [left ; apply H2 ; auto | right ; apply H5 ; auto].
    * apply in_or_app. destruct H7 ; [left ; apply H2 ; auto | right ; apply H5 ; auto].
  + assert (a0: aleq A0 a (interp A0 amap (A --> B))).
    { apply H3. intros γ H8 ; apply H7 ; auto. }
    cbn in a0 ; apply ord_resid in a0.
    apply aleq_trans with (meet a (interp A0 amap A)) ; auto.
    apply glb ; [ apply aleq_refl | apply H6 ; auto].
- destruct IHwBIH_prv as (Δ & H1 & (l & H2) & H3).
  exists (fun x => False). repeat split ; intros ; try contradiction ; auto.
  + exists nil. intros ; split ; intro ; subst ; auto.
  + assert (forall γ : form, Ensembles.Empty_set _ γ -> aleq A0 one (interp A0 amap γ)).
    { intros C HC ; inversion HC. }
    assert (aleq A0 a (interp A0 amap A)).
    { apply H3 ; intros. apply H1 in H5 ; contradiction. }
    eapply aleq_trans ; [ apply high_one | ].
    apply ord_resid. rewrite mcomm ; rewrite greatest.
    apply ord_dresid. rewrite lowest ; auto.
Qed.

(* Then, we proceed to show that sBIH is sound with respect to the
   equational semantic consequence, with respect to the set of equations
   sEq. *)

Definition sEq ϕ ψ := ϕ = # 0 /\ ψ = ⊤.

Theorem alg_soundness_sBIH Γ ϕ : sBIH_prv Γ ϕ -> alg_eqconseq sEq Γ ϕ.
Proof.
intro. induction H ; intros χ δ E ; inversion E ; subst ; cbn in * ; intros BH amap J.
- apply J. exists (# 0). exists ⊤.
  split ; auto. cbn. exists A ; auto.
- cbn. apply aleq_antisym. symmetry ; apply greatest. apply Axioms_one ; auto.
- cbn.
  assert (forall χ δ : form, (fun A B : form =>  exists C D : form,
  sEq C D /\ (exists γ : form, Γ γ /\ first_subst γ C = A /\ first_subst γ D = B)) χ δ ->
  interp BH amap χ = interp BH amap δ).
  { intros. destruct H1 as (C & D & H2 & F & H4 & H5 & H6). inversion H2 ; subst.
    cbn. pose (J F ⊤) ; cbn in e. apply e. exists (# 0), ⊤. split ; auto.
    exists F ; cbn ; repeat split ; auto. }
  pose (IHsBIH_prv1 _ _ E _ _ H1). cbn in e. 
  pose (IHsBIH_prv2 _ _ E _ _ H1). cbn in e0. 
  apply aleq_antisym. symmetry ; apply greatest.
  apply aleq_trans with (meet (interp BH amap A) (rpc (interp BH amap A) (interp BH amap B))).
  * apply glb ; [ rewrite <- e0 | rewrite <- e] ; apply aleq_refl.
  * apply mp.
- cbn.
  assert (forall χ δ : form, (fun A B : form =>  exists C D : form,
  sEq C D /\ (exists γ : form, Γ γ /\ first_subst γ C = A /\ first_subst γ D = B)) χ δ ->
  interp BH amap χ = interp BH amap δ).
  { intros. destruct H0 as (C & D & H2 & F & H4 & H5 & H6). inversion H2 ; subst.
    cbn. pose (J F ⊤) ; cbn in e. apply e. exists (# 0), ⊤. split ; auto.
    exists F ; cbn ; repeat split ; auto. }
  pose (IHsBIH_prv _ _ E _ _ H0). cbn in e. 
  apply aleq_antisym. symmetry ; apply greatest.
  apply ord_resid. rewrite mcomm. rewrite greatest.
  apply ord_dresid. rewrite lowest. rewrite e. apply aleq_refl.
Qed.

(* We can obviously also, show that wBIH is sound with respect to the
   equational semantic consequence, even if it is not going to be complete
   for it. *)

Theorem alg_soundness_wBIH_eq Γ ϕ : wBIH_prv Γ ϕ -> alg_eqconseq sEq Γ ϕ.
Proof.
intro. apply sBIH_extens_wBIH in H. apply alg_soundness_sBIH ; auto.
Qed.

End Soundness.

