Require Import Ensembles.

Require Import Syntax.
Require Import BIH_export.

Section implicative.

Theorem sBIH_IL1 ϕ : sBIH_prv (Empty_set _) (ϕ --> ϕ).
Proof.
apply simp_Id_gen.
Qed.

Theorem sBIH_IL2 ϕ ψ χ : sBIH_prv (fun δ => δ = ϕ --> ψ \/ δ = ψ --> χ) (ϕ --> χ).
Proof.
eapply meta_sImp_trans.
- apply sId ; left ; split.
- apply sId ; right ; split.
Qed.

Theorem sBIH_IL4 ϕ ψ : sBIH_prv (fun δ => δ = ϕ \/ δ = ϕ --> ψ) ψ.
Proof.
eapply sMP.
- apply sId ; right ; split.
- apply sId ; left ; split.
Qed.

Theorem sBIH_IL5 ϕ ψ : sBIH_prv (Singleton _ ϕ) (ψ --> ϕ).
Proof.
eapply sMP.
- apply sThm_irrel.
- apply sId ; split.
Qed.

Theorem sBIH_IL3_Top :
    sBIH_prv (Empty_set _) (⊤ --> ⊤).
Proof.
apply simp_Id_gen.
Qed.

Theorem sBIH_IL3_Bot :
    sBIH_prv (Empty_set _) (⊥ --> ⊥).
Proof.
apply simp_Id_gen.
Qed.

Definition EqImp ϕ1 ϕ2 ψ1 ψ2 := fun δ => δ = ϕ1 --> ϕ2 \/ δ = ψ1 --> ψ2 \/ δ = ϕ2 --> ϕ1 \/ δ = ψ2 --> ψ1.

Theorem sBIH_IL3_And ϕ1 ϕ2 ψ1 ψ2 :
    sBIH_prv (EqImp ϕ1 ϕ2 ψ1 ψ2) ((ϕ1 ∧ ψ1) --> (ϕ2 ∧ ψ2)).
Proof.
eapply sMP.
- eapply sMP.
  + apply sAx ; eapply A8 ; reflexivity.
  + eapply meta_sImp_trans.
    * apply sAx ; eapply A6 ; reflexivity.
    * apply sId ; firstorder.
- eapply meta_sImp_trans.
  + apply sAx ; eapply A7 ; reflexivity.
  + apply sId ; firstorder.
Qed.

Theorem sBIH_IL3_Or ϕ1 ϕ2 ψ1 ψ2 :
    sBIH_prv (EqImp ϕ1 ϕ2 ψ1 ψ2) ((ϕ1 ∨ ψ1) --> (ϕ2 ∨ ψ2)).
Proof.
eapply sMP.
- eapply sMP.
  + apply sAx ; eapply A5 ; reflexivity.
  + eapply meta_sImp_trans.
    * apply sId. left ; reflexivity.
    * apply sAx ; eapply A3 ; reflexivity.
- apply meta_sImp_trans with ψ2.
  + apply sId ; firstorder.
  + apply sAx ; eapply A4 ; reflexivity.
Qed.

Theorem sBIH_IL3_Imp ϕ1 ϕ2 ψ1 ψ2 :
    sBIH_prv (EqImp ϕ1 ϕ2 ψ1 ψ2) ((ϕ1 --> ψ1) --> (ϕ2 --> ψ2)).
Proof.
eapply sMP.
- apply sAnd_Imp.
- apply meta_sImp_trans with ψ1.
  + apply meta_sImp_trans with ((ϕ1 --> ψ1) ∧ ϕ1).
    * eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ apply sAx ; eapply A6 ; reflexivity.
      -- apply meta_sImp_trans with ϕ2.
        ++ apply sAx ; eapply A7 ; reflexivity.
        ++ apply sId ; firstorder.
    * eapply sMP ; [ apply sImp_And | apply simp_Id_gen].
  + apply sId ; firstorder.
Qed.

Theorem sBIH_IL3_Excl ϕ1 ϕ2 ψ1 ψ2 :
    sBIH_prv (EqImp ϕ1 ϕ2 ψ1 ψ2) ((ϕ1 --< ψ1) --> (ϕ2 --< ψ2)).
Proof.
eapply meta_sImp_trans with (ϕ1 --< ψ2).
- apply smonoL_Excl. apply sId ; firstorder.
- apply smonoR_Excl. apply sId ; firstorder.
Qed.

End implicative.