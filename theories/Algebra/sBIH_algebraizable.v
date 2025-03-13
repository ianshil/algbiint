Require Import Ensembles.

Require Import Syntax.
Require Import Bi_Heyting_Algebras.
Require Import algebraic_semantic.
Require Import BIH_export.
Require Import alg_soundness.
Require Import sBIH_alg_completeness.

Section algebraizable.

Variable Hypirrel : forall Γ Φ Ψ, (@setform Γ Φ = @setform Γ Ψ) -> Φ = Ψ. 

Theorem sBIH_Alg1 Γ ϕ : sBIH_prv Γ ϕ <-> alg_eqconseq sEq Γ ϕ.
Proof.
split ; [apply alg_soundness_sBIH | apply alg_completeness_sBIH ; auto].
Qed.

Theorem sBIH_Alg2 Eq ϕ ψ : alg_eqconseq_eq Eq ϕ ψ <->
                           sBIH_prv (fun χ => exists δ γ, Eq δ γ /\ χ = δ <--> γ) (ϕ <--> ψ).
Proof.
split ; intro.
- apply alg_completeness_sBIH ; auto.
  + intros χ γ H0 A amap H1. inversion H0 ; subst ; cbn in *.
    pose (H A amap). rewrite e ; clear e.
    * apply aleq_antisym.
      -- apply high_one.
      -- apply glb.
        ++ apply ord_resid. apply meet_elim2.
        ++ apply ord_resid. apply meet_elim2.
    * intros.
      assert (interp A amap (χ <--> δ) = interp A amap ⊤).
      { apply H1. exists (# 0), ⊤. split ; unfold sEq ; auto.
        exists (χ <--> δ) ; cbn ; repeat split.
        exists χ,δ ; auto. } 
      cbn in H3. apply aleq_antisym.
      -- eapply aleq_trans.
        ++ apply glb.
          ** apply high_one.
          ** apply aleq_refl.
        ++ apply ord_resid. rewrite <- H3. apply meet_elim1.
      -- eapply aleq_trans.
        ++ apply glb.
          ** apply high_one.
          ** apply aleq_refl.
        ++ apply ord_resid. rewrite <- H3. apply meet_elim2.
- intros A amap H0. apply alg_soundness_sBIH in H.
  assert (alg_soundness.sEq # 0 ⊤).
  { unfold alg_soundness.sEq ; split ; auto. }
  pose (H (# 0) ⊤ H1 A amap). cbn in e.
  assert (meet (rpc (interp A amap ϕ) (interp A amap ψ))
  (rpc (interp A amap ψ) (interp A amap ϕ)) = one).
  { apply e. intros χ δ (γ & ρ & H2 & ω & (σ & φ & (H4 & H7)) & (H5 & H6)).
    inversion H2 ; subst ; cbn in *.
    apply H0 in H4. rewrite H4.
    apply aleq_antisym.
    + apply high_one.
    + apply glb.
        * apply ord_resid. apply meet_elim2.
        * apply ord_resid. apply meet_elim2. }
  apply aleq_antisym.
  + eapply aleq_trans.
    * apply glb.
      -- apply high_one.
      -- apply aleq_refl.
    * apply ord_resid. rewrite <- H2. apply meet_elim1.
  + eapply aleq_trans.
    * apply glb.
      -- apply high_one.
      -- apply aleq_refl.
    * apply ord_resid. rewrite <- H2. apply meet_elim2.
Qed.

Theorem sBIH_Alg3 ϕ : sBIH_prv (Singleton _ ϕ) (ϕ <--> ⊤) /\
                      sBIH_prv (Singleton _ (ϕ <--> ⊤)) ϕ.
Proof.
split.
- eapply sMP.
  + eapply sMP.
    * eapply sMP.
      -- apply sAx ; eapply A8 ; reflexivity.
      -- eapply sThm_irrel.
    * eapply sMP.
      -- apply sAnd_Imp.
      -- eapply sMP.
        ++ apply sThm_irrel.
        ++ apply sId ; split.
  + apply sBIH_extens_wBIH ; apply prv_Top.
- eapply sMP.
  + eapply sMP.
    * apply sAx ; eapply A7 ; reflexivity.
    * apply sId ; split.
  + apply sBIH_extens_wBIH ; apply prv_Top.
Qed.

Theorem sBIH_Alg4 ϕ ψ : alg_eqconseq_eq (fun δ γ => δ = ϕ /\ γ = ψ) (ϕ <--> ψ) ⊤ /\
                        alg_eqconseq_eq (fun δ γ => δ = (ϕ <--> ψ) /\ γ = ⊤) ϕ ψ.
Proof.
split.
- intros A amap H. cbn.
  assert (interp A amap ϕ = interp A amap ψ).
  { apply H ; auto. }
  rewrite H0.
  apply aleq_antisym.
  + apply high_one.
  + apply glb.
    * apply ord_resid. apply meet_elim2.
    * apply ord_resid. apply meet_elim2.
- intros A amap H.
  assert (interp A amap (ϕ <--> ψ) = interp A amap ⊤).
  { apply H ; auto. }
  cbn in H0.
  apply aleq_antisym.
  + eapply aleq_trans.
    * apply glb.
      -- apply high_one.
      -- apply aleq_refl.
    * apply ord_resid. rewrite <- H0. apply meet_elim1.
  + eapply aleq_trans.
    * apply glb.
      -- apply high_one.
      -- apply aleq_refl.
    * apply ord_resid. rewrite <- H0. apply meet_elim2.
Qed.

End algebraizable.