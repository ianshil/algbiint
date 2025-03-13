Require Import Ensembles.

Require Import Syntax.
Require Import Bi_Heyting_Algebras.
Require Import algebraic_semantic.
Require Import BIH_export.

Axiom LEM : forall P, P \/ ~ P.

Section Equiprovable_classes. 

Variable Γ : @Ensemble form.

Class eqprv : Type :=
  { setform : @Ensemble form ;
    equiprov ϕ : setform ϕ <-> (forall ψ, setform ψ ->
                   (sBIH_prv Γ (ψ --> ϕ) /\
                    sBIH_prv Γ (ϕ --> ψ)))
  }.

Lemma inhab_eqprv (Φ : eqprv) : exists ϕ, (@setform Φ) ϕ.
Proof.
epose (LEM _) ; destruct o as [P | NP] ; [ exact P | exfalso].
destruct (equiprov ⊤). apply NP. exists ⊤. apply H0.
intros. exfalso. apply NP ; exists ψ ; auto.
Qed.

(* Equiprovable class of Γ. *)

Definition sfform_eqprv ϕ := fun ψ => sBIH_prv Γ (ϕ --> ψ) /\ sBIH_prv Γ (ψ --> ϕ).

Lemma in_sfform_eqprv ϕ : sfform_eqprv ϕ ϕ.
Proof.
split ; apply simp_Id_gen.
Qed.

Lemma eprvform_eqprv ϕ : forall χ, sfform_eqprv ϕ χ <-> (forall ψ, sfform_eqprv ϕ ψ ->
                   (sBIH_prv Γ (ψ --> χ) /\
                    sBIH_prv Γ (χ --> ψ))).
Proof.
intros χ ; split ; intro H.
- intros ψ Hψ ; split ; unfold sfform_eqprv in * ; destruct H ; destruct Hψ.
  + eapply meta_sImp_trans. exact H2. auto.
  + eapply meta_sImp_trans. exact H0. auto.
- split ; apply H ; split ; apply simp_Id_gen.
Qed.

Instance  epform_eqprv ϕ : eqprv :=
    {| 
        setform := sfform_eqprv ϕ ;
        equiprov := eprvform_eqprv ϕ
    |}.

Definition sfone := fun ϕ => sBIH_prv Γ ϕ.

Lemma eprvone : forall ϕ, sfone ϕ <-> (forall ψ, sfone ψ ->
                   (sBIH_prv Γ (ψ --> ϕ) /\
                    sBIH_prv Γ (ϕ --> ψ))).
Proof.
intros ϕ ; split ; intro H.
- intros ψ Hψ ; split. 
  + eapply sMP. apply sThm_irrel. auto.
  + eapply sMP. apply sThm_irrel. auto.
- destruct (H ⊤).
  + apply sBIH_extens_wBIH. apply prv_Top.
  + eapply sMP.
    * exact H0.
    * apply sBIH_extens_wBIH. apply prv_Top.
Qed.

Instance  epone : eqprv :=
    {| 
        setform := sfone ;
        equiprov := eprvone
    |}.

(* Equiprovable class of ⊥. *)

Definition sfzero := fun ϕ => sBIH_prv Γ (ϕ --> ⊥).

Lemma eprvzero : forall ϕ, sfzero ϕ <-> (forall ψ, sfzero ψ ->
                   (sBIH_prv Γ (ψ --> ϕ) /\
                    sBIH_prv Γ (ϕ --> ψ))).
Proof.
intros ϕ ; split ; intro H.
- intros ψ Hψ ; split. 
  + eapply sMP. 2: apply sEFQ. eapply sMP.
    apply sImp_trans. auto.
  + eapply sMP. 2: apply sEFQ. eapply sMP.
    apply sImp_trans. auto.
- destruct (H ⊥) ; auto.
  apply simp_Id_gen.
Qed.

Instance  epzero : eqprv :=
    {| 
        setform := sfzero ;
        equiprov := eprvzero
    |}.

(* Join of equivalence classes. *)

Definition sfjoin (Φ Ψ : eqprv) := fun χ => exists ϕ ψ,
    (@setform Φ) ϕ /\ (@setform Ψ) ψ /\
    sBIH_prv Γ ((ϕ ∨ ψ) --> χ) /\ sBIH_prv Γ (χ --> (ϕ ∨ ψ)).

Lemma eprvjoin Φ Ψ : forall ϕ, (sfjoin Φ Ψ) ϕ <-> (forall ψ, (sfjoin Φ Ψ) ψ ->
                   (sBIH_prv Γ (ψ --> ϕ) /\
                    sBIH_prv Γ (ϕ --> ψ))).
Proof.
intros χ ; split ; intro H.
- intros δ Hδ ; split. 
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A5 ; reflexivity.
            --- eapply sMP.
              +++ eapply sMP.
                *** apply sImp_trans.
                *** rewrite (@equiprov Φ) in H0. apply H0. exact H4.
              +++ apply sAx ; eapply A3 ; reflexivity.
          ** eapply sMP.
            --- eapply sMP.
              +++ apply sImp_trans.
              +++ rewrite (@equiprov Ψ) in H1. apply H1. exact H5.
            --- apply sAx ; eapply A4 ; reflexivity.
      -- auto.
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H7.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A5 ; reflexivity.
            --- eapply sMP.
              +++ eapply sMP.
                *** apply sImp_trans.
                *** rewrite (@equiprov Φ) in H4. apply H4. exact H0.
              +++ apply sAx ; eapply A3 ; reflexivity.
          ** eapply sMP.
            --- eapply sMP.
              +++ apply sImp_trans.
              +++ rewrite (@equiprov Ψ) in H5. apply H5. exact H1.
            --- apply sAx ; eapply A4 ; reflexivity.
      -- auto.
- destruct (inhab_eqprv Φ) as (ϕ & H1) ; destruct (inhab_eqprv Ψ) as (ψ & H2).
  exists ϕ, ψ ; repeat split ; auto.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply simp_Id_gen.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply simp_Id_gen.
Qed.

Instance  epjoin Φ Ψ: eqprv :=
    {| 
        setform := sfjoin Φ Ψ ;
        equiprov := eprvjoin Φ Ψ
    |}.

(* Meet of equivalence classes. *)

Definition sfmeet (Φ Ψ : eqprv) := fun χ => exists ϕ ψ,
    (@setform Φ) ϕ /\ (@setform Ψ) ψ /\
    sBIH_prv Γ ((ϕ ∧ ψ) --> χ) /\ sBIH_prv Γ (χ --> (ϕ ∧ ψ)).

Lemma eprvmeet Φ Ψ : forall ϕ, (sfmeet Φ Ψ) ϕ <-> (forall ψ, (sfmeet Φ Ψ) ψ ->
                   (sBIH_prv Γ (ψ --> ϕ) /\
                    sBIH_prv Γ (ϕ --> ψ))).
Proof.
intros χ ; split ; intro H.
- intros δ Hδ ; split. 
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- eapply sMP.
              +++ eapply sMP.
                *** apply sImp_trans.
                *** apply sAx ; eapply A6 ; reflexivity.
              +++ rewrite (@equiprov Φ) in H0. apply H0. exact H4.
          ** eapply sMP.
            --- eapply sMP.
              +++ apply sImp_trans.
              +++ apply sAx ; eapply A7 ; reflexivity.
            --- rewrite (@equiprov Ψ) in H1. apply H1. exact H5.
      -- auto.
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H7.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- eapply sMP.
              +++ eapply sMP.
                *** apply sImp_trans.
                *** apply sAx ; eapply A6 ; reflexivity.
              +++ rewrite (@equiprov Φ) in H4. apply H4. exact H0.
          ** eapply sMP.
            --- eapply sMP.
              +++ apply sImp_trans.
              +++ apply sAx ; eapply A7 ; reflexivity.
            --- rewrite (@equiprov Ψ) in H5. apply H5. exact H1.
      -- auto.
- destruct (inhab_eqprv Φ) as (ϕ & H1) ; destruct (inhab_eqprv Ψ) as (ψ & H2).
  exists ϕ, ψ ; repeat split ; auto.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply simp_Id_gen.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply simp_Id_gen.
Qed.

Instance  epmeet Φ Ψ: eqprv :=
    {| 
        setform := sfmeet Φ Ψ ;
        equiprov := eprvmeet Φ Ψ
    |}.

(* Implication of equivalence classes. *)

Definition sfrpc (Φ Ψ : eqprv) := fun χ => exists ϕ ψ,
    (@setform Φ) ϕ /\ (@setform Ψ) ψ /\
    sBIH_prv Γ ((ϕ --> ψ) --> χ) /\ sBIH_prv Γ (χ --> (ϕ --> ψ)).

Lemma eprvrpc Φ Ψ : forall ϕ, (sfrpc Φ Ψ) ϕ <-> (forall ψ, (sfrpc Φ Ψ) ψ ->
                   (sBIH_prv Γ (ψ --> ϕ) /\
                    sBIH_prv Γ (ϕ --> ψ))).
Proof.
intros χ ; split ; intro H.
- intros δ Hδ ; split. 
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ eapply sMP.
          ** apply sAnd_Imp.
          ** eapply sMP.
            --- eapply sMP.
              +++ apply sImp_trans.
              +++ eapply sMP.
                *** eapply sMP.
                  ---- apply sImp_trans.
                  ---- eapply sMP.
                    ++++ eapply sMP.
                      **** apply sAx ; eapply A8 ; reflexivity.
                      **** apply sAx ; eapply A6 ; reflexivity.
                    ++++ eapply sMP. apply sImp_And. eapply sMP.
                         apply sThm_irrel.
                         rewrite (@equiprov Φ) in H4. apply H4. exact H0.
                *** eapply sMP.
                    ++++ apply sImp_And.
                    ++++ apply simp_Id_gen.
            --- rewrite (@equiprov Ψ) in H1. apply H1. exact H5.
      -- auto.
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H7.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ eapply sMP.
          ** apply sAnd_Imp.
          ** eapply sMP.
            --- eapply sMP.
              +++ apply sImp_trans.
              +++ eapply sMP.
                *** eapply sMP.
                  ---- apply sImp_trans.
                  ---- eapply sMP.
                    ++++ eapply sMP.
                      **** apply sAx ; eapply A8 ; reflexivity.
                      **** apply sAx ; eapply A6 ; reflexivity.
                    ++++ eapply sMP. apply sImp_And. eapply sMP.
                         apply sThm_irrel.
                         rewrite (@equiprov Φ) in H0. apply H0. exact H4.
                *** eapply sMP.
                    ++++ apply sImp_And.
                    ++++ apply simp_Id_gen.
            --- rewrite (@equiprov Ψ) in H5. apply H5. exact H1.
      -- auto.
- destruct (inhab_eqprv Φ) as (ϕ & H1) ; destruct (inhab_eqprv Ψ) as (ψ & H2).
  exists ϕ, ψ ; repeat split ; auto.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply simp_Id_gen.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply simp_Id_gen.
Qed.

Instance  eprpc Φ Ψ: eqprv :=
    {| 
        setform := sfrpc Φ Ψ ;
        equiprov := eprvrpc Φ Ψ
    |}.

(* Exclusion of equivalence classes. *)

Definition sfsubtr (Φ Ψ : eqprv) := fun χ => exists ϕ ψ,
    (@setform Φ) ϕ /\ (@setform Ψ) ψ /\
    sBIH_prv Γ ((ϕ --< ψ) --> χ) /\ sBIH_prv Γ (χ --> (ϕ --< ψ)).

Lemma eprvsubtr Φ Ψ : forall ϕ, (sfsubtr Φ Ψ) ϕ <-> (forall ψ, (sfsubtr Φ Ψ) ψ ->
                   (sBIH_prv Γ (ψ --> ϕ) /\
                    sBIH_prv Γ (ϕ --> ψ))).
Proof.
intros χ ; split ; intro H.
- intros δ Hδ ; split. 
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sImp_trans.
            --- apply smonoL_Excl. rewrite (@equiprov Ψ) in H5. apply H5. auto.
          ** apply smonoR_Excl. rewrite (@equiprov Φ) in H0. apply H0. exact H4.
      -- auto.
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H7.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sImp_trans.
            --- apply smonoL_Excl. rewrite (@equiprov Ψ) in H1. apply H1. auto.
          ** apply smonoR_Excl. rewrite (@equiprov Φ) in H4. apply H4. exact H0.
      -- auto.
- destruct (inhab_eqprv Φ) as (ϕ & H1) ; destruct (inhab_eqprv Ψ) as (ψ & H2).
  exists ϕ, ψ ; repeat split ; auto.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply simp_Id_gen.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply simp_Id_gen.
Qed.

Instance  epsubtr Φ Ψ : eqprv :=
    {| 
        setform := sfsubtr Φ Ψ ;
        equiprov := eprvsubtr Φ Ψ
    |}.

End Equiprovable_classes.




Section Properties_eqprv.

Variable Γ : @Ensemble form.
Variable eqprv_prf_irrel : forall Φ Ψ, (@setform Γ Φ = @setform Γ Ψ) -> Φ = Ψ. 

Lemma epjcomm Φ Ψ : epjoin Γ Φ Ψ = epjoin Γ Ψ Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). exists D,C ; repeat split ; auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- apply scomm_Or_obj.
    * auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * apply scomm_Or_obj.
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). exists D,C ; repeat split ; auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- apply scomm_Or_obj.
    * auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * apply scomm_Or_obj.
Qed.

Lemma epjassoc Φ Ψ Χ : epjoin Γ Φ (epjoin Γ Ψ Χ) = epjoin Γ (epjoin Γ Φ Ψ) Χ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3).
  unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn in *.
  destruct H1 as (E & F & H4 & H5 & H6 & H7). unfold setform in *.
  exists (C ∨ E), F ; repeat split ; auto.
  + exists C, E ; repeat split ; auto ; apply simp_Id_gen.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- apply sOr_imp_assoc. apply simp_Id_gen.
    * eapply sMP.
      -- eapply sMP.
        ++ eapply sImp_trans.
        ++ apply smonotL_Or. exact H6.
      -- auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * eapply sMP.
      -- eapply sMP.
        ++ eapply sImp_trans.
        ++ apply smonotL_Or. exact H7.
      -- eapply sMP.
        ++ eapply sMP.
          ** apply sAx ; eapply A5 ; reflexivity.
          ** eapply sMP.
            --- eapply sMP.
              +++ apply sImp_trans.
              +++  apply sAx ; eapply A3 ; reflexivity.
            --- apply sAx ; eapply A3 ; reflexivity.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A5 ; reflexivity.
            --- eapply sMP.
              +++ eapply sMP.
                *** apply sImp_trans.
                *** apply sAx ; eapply A4 ; reflexivity.
              +++ apply sAx ; eapply A3 ; reflexivity.
          ** apply sAx ; eapply A4 ; reflexivity.
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3).
  unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn in *.
  destruct H0 as (E & F & H4 & H5 & H6 & H7). unfold setform in *.
  exists E, (F ∨ D) ; repeat split ; auto.
  + exists F, D ; repeat split ; auto ; apply simp_Id_gen.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- eapply sMP.
        ++ eapply sMP.
          ** apply sAx ; eapply A5 ; reflexivity.
          ** eapply sMP.
            --- eapply sMP.
              +++ apply sImp_trans.
              +++ apply sAx ; eapply A3 ; reflexivity.
            --- apply sAx ; eapply A3 ; reflexivity.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A5 ; reflexivity.
            --- eapply sMP.
              +++ eapply sMP.
                *** apply sImp_trans.
                *** apply sAx ; eapply A4 ; reflexivity.
              +++ apply sAx ; eapply A3 ; reflexivity.
          ** apply sAx ; eapply A4 ; reflexivity.
    * eapply sMP.
      -- eapply sMP.
        ++ eapply sImp_trans.
        ++ apply smonotR_Or. exact H6.
      -- auto.
  + apply sOr_imp_assoc. eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * apply smonotR_Or. auto.
Qed.

Lemma epjabsorp Φ Ψ : epjoin Γ Φ (epmeet Γ Φ Ψ) = Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). 
  unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct H1 as (E & F & H4 & H5 & H6 & H7).
  apply equiprov. intros B HB. split.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- rewrite equiprov in HB. apply HB. exact H0.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sImp_trans.
        ++ apply sAx ; eapply A3 ; reflexivity.
      -- exact H2.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A5 ; reflexivity.
        ++ rewrite equiprov in HB. apply HB. auto.
      -- eapply sMP.
        ++ eapply sMP.
          ** apply sImp_trans.
          ** exact H7.
        ++ eapply sMP.
          ** eapply sMP.
            --- eapply sImp_trans.
            --- apply sAx ; eapply A6 ; reflexivity.
          ** rewrite equiprov in HB. apply HB. auto.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn ;
  unfold sfmeet in * ; cbn in * ; unfold setform in * ; cbn in *.
  destruct (inhab_eqprv _ Ψ) as (B & HB).
  exists A, (A ∧ B) ; repeat split ; auto.
  + exists A, B ; repeat split ; auto ; apply simp_Id_gen.
  + eapply sMP.
    * eapply sMP.
      -- apply sAx ; eapply A5 ; reflexivity.
      -- apply simp_Id_gen.
    * apply sAx ; eapply A6 ; reflexivity.
  + apply sAx ; eapply A3 ; reflexivity.
Qed.

Lemma epmcomm Φ Ψ : epmeet Γ Φ Ψ = epmeet Γ Ψ Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). exists D,C ; repeat split ; auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- apply scomm_And_obj.
    * auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * apply scomm_And_obj.
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). exists D,C ; repeat split ; auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- apply scomm_And_obj.
    * auto.
  + eapply sMP.
    * eapply sMP.
      -- apply sImp_trans.
      -- exact H3.
    * apply scomm_And_obj.
Qed.

Lemma epmassoc Φ Ψ Χ : epmeet Γ Φ (epmeet Γ Ψ Χ) = epmeet Γ (epmeet Γ Φ Ψ) Χ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3).
  unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn in *.
  destruct H1 as (E & F & H4 & H5 & H6 & H7). unfold setform in *.
  exists (C ∧ E), F ; repeat split ; auto.
  + exists C, E ; repeat split ; auto ; apply simp_Id_gen.
  + eapply meta_sImp_trans.
    * apply sassoc_And_obj.
    * eapply meta_sImp_trans.
      -- eapply sMP.
        ++ eapply sMP.
          ** apply sAx ; eapply A8 ; reflexivity.
          ** apply sAx ; eapply A6 ; reflexivity.
        ++ eapply meta_sImp_trans.
          ** apply sAx ; eapply A7 ; reflexivity.
          ** exact H6.
      -- auto.
  + eapply meta_sImp_trans.
    * exact H3.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- apply sAx ; eapply A6 ; reflexivity.
          ** eapply meta_sImp_trans.
            --- apply sAx ; eapply A7 ; reflexivity.
            --- eapply meta_sImp_trans.
              +++ exact H7.
              +++ apply sAx ; eapply A6 ; reflexivity.
      -- eapply meta_sImp_trans.
        ++ apply sAx ; eapply A7 ; reflexivity.
        ++ eapply meta_sImp_trans.
          ** exact H7.
          ** apply sAx ; eapply A7 ; reflexivity.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3).
  unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn in *.
  destruct H0 as (E & F & H4 & H5 & H6 & H7). unfold setform in *.
  exists E, (F ∧ D) ; repeat split ; auto.
  + exists F, D ; repeat split ; auto ; apply simp_Id_gen.
  + eapply meta_sImp_trans.
    * apply sassoc_And_obj.
    * eapply meta_sImp_trans.
      -- eapply sMP.
        ++ eapply sMP.
          ** apply sAx ; eapply A8 ; reflexivity.
          ** eapply meta_sImp_trans.
            --- apply sAx ; eapply A6 ; reflexivity.
            --- exact H6.
        ++ apply sAx ; eapply A7 ; reflexivity.
      -- auto.
  + eapply meta_sImp_trans.
    * exact H3.
    * eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ eapply meta_sImp_trans.
          ** apply sAx ; eapply A6 ; reflexivity.
          ** eapply meta_sImp_trans.
            --- exact H7.
            --- apply sAx ; eapply A6 ; reflexivity.
      -- eapply sMP.
        ++ eapply sMP.
          ** apply sAx ; eapply A8 ; reflexivity.
          ** eapply meta_sImp_trans.
            --- apply sAx ; eapply A6 ; reflexivity.
            --- eapply meta_sImp_trans.
              +++ exact H7.
              +++ apply sAx ; eapply A7 ; reflexivity.
        ++ apply sAx ; eapply A7 ; reflexivity.
Qed.

Lemma epmabsorp Φ Ψ : epmeet Γ Φ (epjoin Γ Φ Ψ) = Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). 
  unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct H1 as (E & F & H4 & H5 & H6 & H7).
  apply equiprov. intros B HB. split.
  + eapply meta_sImp_trans. 2: exact H2.
    eapply sMP.
    * eapply sMP.
      -- apply sAx ; eapply A8 ; reflexivity.
      -- rewrite equiprov in HB. apply HB. auto.
    * eapply meta_sImp_trans. 2: exact H6.
      eapply meta_sImp_trans.
      -- rewrite equiprov in HB. apply HB. exact H4.
      -- apply sAx ; eapply A3 ; reflexivity.
  + eapply meta_sImp_trans. exact H3.
    eapply meta_sImp_trans.
    * apply sAx ; eapply A6 ; reflexivity.
    * rewrite equiprov in HB. apply HB. auto.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn ;
  unfold sfjoin in * ; cbn in * ; unfold setform in * ; cbn in *.
  destruct (inhab_eqprv _ Ψ) as (B & HB).
  exists A, (A ∨ B) ; repeat split ; auto.
  + exists A, B ; repeat split ; auto ; apply simp_Id_gen.
  + apply sAx ; eapply A6 ; reflexivity.
  + eapply sMP.
    * eapply sMP.
      -- apply sAx ; eapply A8 ; reflexivity.
      -- apply simp_Id_gen.
    * apply sAx ; eapply A3 ; reflexivity.
Qed.

Lemma eplowest Φ : epjoin Γ Φ (epzero Γ) = Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). 
  unfold setform in * ; cbn in * ; unfold sfzero in * ; cbn.
  apply equiprov. intros B HB. split.
  + eapply meta_sImp_trans. 2: exact H2.
    eapply meta_sImp_trans.
    * rewrite equiprov in HB. apply HB. exact H0.
    * apply sAx ; eapply A3 ; reflexivity.
  + eapply meta_sImp_trans. exact H3.
    eapply sMP.
    * eapply sMP.
      -- apply sAx ; eapply A5 ; reflexivity.
      -- rewrite equiprov in HB. apply HB. auto.
    * eapply meta_sImp_trans. exact H1. apply sEFQ.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn ;
  unfold sfzero in * ; cbn in * ; unfold setform in * ; cbn in *.
  exists A, ⊥ ; repeat split ; auto.
  + apply simp_Id_gen.
  + eapply sMP.
    * eapply sMP.
      -- apply sAx ; eapply A5 ; reflexivity.
      -- apply simp_Id_gen.
    * apply sEFQ.
  + apply sAx ; eapply A3 ; reflexivity.
Qed.

Lemma epgreatest Φ : epmeet Γ Φ (epone Γ) = Φ.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). 
  unfold setform in * ; cbn in * ; unfold sfone in * ; cbn.
  apply equiprov. intros B HB. split.
  + eapply meta_sImp_trans. 2: exact H2.
    eapply sMP.
    * eapply sMP.
      -- apply sAx ; eapply A8 ; reflexivity.
      -- rewrite equiprov in HB. apply HB. auto.
    * eapply sMP. 2: exact H1. apply sThm_irrel.
  + eapply meta_sImp_trans. exact H3.
    eapply meta_sImp_trans.
    * apply sAx ; eapply A6 ; reflexivity.
    * rewrite equiprov in HB. apply HB. exact H0.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn ;
  unfold sfone in * ; cbn in * ; unfold setform in * ; cbn in *.
  exists A, ⊤ ; repeat split ; auto.
  + apply sBIH_extens_wBIH. apply prv_Top.
  + apply sAx ; eapply A6 ; reflexivity.
  + eapply sMP.
    * eapply sMP.
      -- apply sAx ; eapply A8 ; reflexivity.
      -- apply simp_Id_gen.
    * eapply sMP. 2: apply sBIH_extens_wBIH ; apply prv_Top. apply sThm_irrel.
Qed.

Lemma epresiduation Φ Ψ Χ : (Φ = epmeet Γ Φ (eprpc Γ Ψ Χ)) <-> (epmeet Γ Φ Ψ = epmeet Γ (epmeet Γ Φ Ψ) Χ).
Proof.
split ; intro H.
- apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
    destruct HA as (C & D & H0 & H1 & H2 & H3). 
    cbn in * ; unfold sfmeet in * ; cbn.
    rewrite H in H0. cbn in * ; unfold sfmeet in * ; cbn in *.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    unfold sfrpc in * ; cbn in *.
    destruct H5 as (G & K & H8 & H9 & H10 & H11).
    exists (E ∧ G), K. repeat split ; auto.
    * exists E, G ; repeat split ; auto ; apply simp_Id_gen.
    * eapply meta_sImp_trans. 2: exact H2.
      eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ eapply meta_sImp_trans. 2: exact H6.
           eapply meta_sImp_trans. apply sassoc_And_obj.
           eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- apply sAx ; eapply A6 ; reflexivity.
          ** eapply meta_sImp_trans. 2: exact H10.
             eapply meta_sImp_trans. 2: apply sThm_irrel.
             eapply meta_sImp_trans.
            --- apply sAx ; eapply A7 ; reflexivity.
            --- apply sAx ; eapply A7 ; reflexivity.
      -- eapply meta_sImp_trans.
        ++ eapply meta_sImp_trans.
          ** apply sAx ; eapply A6 ; reflexivity.
          ** apply sAx ; eapply A7 ; reflexivity.
        ++ rewrite equiprov in H1. apply H1. auto.
    * eapply meta_sImp_trans. exact H3.
      eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- eapply meta_sImp_trans.
              +++ apply sAx ; eapply A6 ; reflexivity.
              +++ eapply meta_sImp_trans. exact H7. apply sAx ; eapply A6 ; reflexivity.
          ** eapply meta_sImp_trans. apply sAx ; eapply A7 ; reflexivity.
             rewrite equiprov in H1. apply H1. auto.
      -- eapply meta_sImp_trans.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- eapply meta_sImp_trans.
              +++ apply sAx ; eapply A6 ; reflexivity.
              +++ eapply meta_sImp_trans.
                *** exact H7.
                *** apply sAx ; eapply A7 ; reflexivity.
          ** eapply meta_sImp_trans.
            --- apply sAx ; eapply A7 ; reflexivity.
            --- rewrite equiprov in H1. apply H1. exact H8.
        ++ eapply sMP.
          ** apply sImp_And.
          ** auto.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn. 
    destruct HA as (C & D & H0 & H1 & H2 & H3).
    cbn in * ; unfold sfmeet in * ; cbn.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    rewrite H. cbn in * ; unfold sfmeet in * ; cbn in *. unfold setform in *.
    exists (E ∧ (F --> D)), F. repeat split ; auto.
    * exists E, (F --> D) ; repeat split ; auto. 2-3: apply simp_Id_gen.
      exists F,D ; repeat split ; auto ; apply simp_Id_gen.
    * eapply meta_sImp_trans. 2: exact H2.
      eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ eapply meta_sImp_trans. 2: exact H6.
           eapply meta_sImp_trans. apply sassoc_And_obj.
           eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- apply sAx ; eapply A6 ; reflexivity.
          ** eapply meta_sImp_trans. apply sAx ; eapply A7 ; reflexivity.
             apply sAx ; eapply A7 ; reflexivity.
      -- eapply meta_sImp_trans.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- eapply meta_sImp_trans.
              +++ apply sAx ; eapply A6 ; reflexivity.
              +++ apply sAx ; eapply A7 ; reflexivity.
          ** apply sAx ; eapply A7 ; reflexivity.
        ++ eapply sMP.
          ** apply sImp_And.
          ** apply simp_Id_gen.
    * eapply meta_sImp_trans. exact H3.
      eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- eapply meta_sImp_trans.
              +++ apply sAx ; eapply A6 ; reflexivity.
              +++ eapply meta_sImp_trans. exact H7. apply sAx ; eapply A6 ; reflexivity.
          ** eapply meta_sImp_trans. apply sAx ; eapply A7 ; reflexivity.
             apply sThm_irrel.
      -- eapply meta_sImp_trans.
        ++ apply sAx ; eapply A6 ; reflexivity.
        ++ eapply meta_sImp_trans.
          ** exact H7.
          ** apply sAx ; eapply A7 ; reflexivity.
- apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
    destruct (inhab_eqprv _ Ψ) as (B & HB).
    assert (H1: @setform Γ (epmeet Γ Φ Ψ) (A ∧ B)).
    {
      exists A,B ; repeat split ; auto ; apply simp_Id_gen.
    }
    rewrite H in H1. cbn in H1.
    destruct H1 as (C & D & H0 & H1 & H2 & H3). 
    cbn in * ; unfold sfmeet in * ; cbn.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    exists E, (F --> D) ; repeat split ; auto.
    * exists F, D ; repeat split ; auto ; apply simp_Id_gen.
    * eapply meta_sImp_trans.
      -- apply sAx ; eapply A6 ; reflexivity.
      -- rewrite equiprov in H4. apply H4. auto.
    *  eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ rewrite equiprov in H4. apply H4. auto.
      -- eapply sMP.
        ++ apply sAnd_Imp.
        ++ eapply meta_sImp_trans.
          ** eapply meta_sImp_trans.
            --- eapply sMP.
              +++ eapply sMP.
                *** apply sAx ; eapply A8 ; reflexivity.
                *** apply sAx ; eapply A6 ; reflexivity.
              +++ eapply meta_sImp_trans.
                *** apply sAx ; eapply A7 ; reflexivity.
                *** rewrite equiprov in HB. apply HB. auto.
            --- exact H3.
          ** apply sAx ; eapply A7 ; reflexivity.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn. 
    destruct HA as (C & D & H0 & H1 & H2 & H3).
    cbn in * ; unfold sfrpc in * ; cbn.
    destruct H1 as (E & F & H4 & H5 & H6 & H7).
    apply equiprov. intros K HK. split.
    * eapply meta_sImp_trans. 2: exact H2.
      eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ rewrite equiprov in H0. apply H0. auto.
      -- eapply meta_sImp_trans. 2: exact H6.
         eapply sMP.
        ++ apply sAnd_Imp.
        ++ assert (H8: @setform Γ (epmeet Γ Φ Ψ) (K ∧ E)).
           { exists K,E ; repeat split ; auto ; apply simp_Id_gen. }
           rewrite H in H8. unfold setform in H8 ; cbn in H8 ; unfold sfmeet in H8 ; cbn.
           destruct H8 as (J & L & H9 & H10 & H11 & H12).
           eapply meta_sImp_trans.
           ** exact H12.
           ** eapply meta_sImp_trans.
            --- apply sAx ; eapply A7 ; reflexivity.
            --- rewrite equiprov in H10. apply H10. auto.
    * eapply meta_sImp_trans. exact H3. eapply meta_sImp_trans.
      -- apply sAx ; eapply A6 ; reflexivity.
      -- rewrite equiprov in H0. apply H0. auto.
Qed.

Lemma epdresiduation Φ Ψ Χ : (epsubtr Γ Φ Ψ = epmeet Γ (epsubtr Γ Φ Ψ) Χ) <-> (Φ = epmeet Γ Φ (epjoin Γ Ψ Χ)).
Proof.
split ; intro H.
- apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
    destruct (inhab_eqprv _ Ψ) as (B & HB).
    assert (H1: @setform Γ (epsubtr Γ Φ Ψ) (A --< B)).
    { exists A,B ; repeat split ; auto ; apply simp_Id_gen. }
    rewrite H in H1. cbn in H1. 
    destruct H1 as (C & D & H0 & H1 & H2 & H3). 
    cbn in * ; unfold sfjoin in * ; cbn.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    exists E, (F ∨ D) ; repeat split ; auto.
    * exists F, D ; repeat split ; auto ; apply simp_Id_gen.
    * eapply meta_sImp_trans.
      -- apply sAx ; eapply A6 ; reflexivity.
      -- rewrite equiprov in H4. apply H4. auto.
    * apply sdual_residuation in H3. eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ rewrite equiprov in H4. apply H4. auto.
      -- eapply meta_sImp_trans.
        ++ exact H3.
        ++ eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A5 ; reflexivity.
            --- eapply meta_sImp_trans.
              +++ rewrite equiprov in HB. apply HB. exact H5.
              +++ apply sAx ; eapply A3 ; reflexivity.
          ** eapply meta_sImp_trans.
            --- apply sAx ; eapply A7 ; reflexivity.
            --- apply sAx ; eapply A4 ; reflexivity.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn. 
    destruct HA as (C & D & H0 & H1 & H2 & H3).
    cbn in * ; unfold sfsubtr in * ; cbn.
    destruct H1 as (E & F & H4 & H5 & H6 & H7).
    apply equiprov. intros K HK. split.
    * eapply meta_sImp_trans. 2: exact H2.
      eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ rewrite equiprov in H0. apply H0. auto.
      -- eapply meta_sImp_trans. 2: exact H6. unfold setform in *.
         apply sdual_residuation.
         assert (H8: @setform Γ (epsubtr Γ Φ Ψ) (K --< E)).
         { exists K,E ; repeat split ; auto ; apply simp_Id_gen. }
         rewrite H in H8. unfold setform in H8 ; cbn in H8 ; unfold sfmeet in H8 ; cbn.
         destruct H8 as (J & L & H9 & H10 & H11 & H12).
         eapply meta_sImp_trans.
         ++ exact H12.
         ++ eapply meta_sImp_trans.
          ** apply sAx ; eapply A7 ; reflexivity.
          ** rewrite equiprov in H10. apply H10. auto.
    * eapply meta_sImp_trans. exact H3. eapply meta_sImp_trans.
      -- apply sAx ; eapply A6 ; reflexivity.
      -- rewrite equiprov in H0. apply H0. auto.
- apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn. 
    destruct HA as (C & D & H0 & H1 & H2 & H3).
    cbn in * ; unfold sfjoin in * ; cbn. rewrite H in H0.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    destruct H5 as (J & L & H9 & H10 & H11 & H12).
    exists ((E ∧ (J ∨ L)) --< D), L ; repeat split ; auto.
    * exists (E ∧ (J ∨ L)), D ; repeat split ; auto. 2-3: apply simp_Id_gen.
      rewrite H. exists E,(J ∨ L) ; repeat split ; auto. 2-3: apply simp_Id_gen.
      exists J, L ; repeat split ; auto ; apply simp_Id_gen.
    * eapply meta_sImp_trans. 2: exact H2.
      eapply meta_sImp_trans.
      -- apply sAx ; eapply A6 ; reflexivity.
      -- apply smonoR_Excl. eapply meta_sImp_trans. 2: exact H6.
         eapply sMP.
        ++ eapply sMP.
          ** apply sAx ; eapply A8 ; reflexivity.
          ** apply sAx ; eapply A6 ; reflexivity.
        ++ eapply meta_sImp_trans. 2: exact H11.
           apply sAx ; eapply A7 ; reflexivity.
    * eapply meta_sImp_trans. exact H3.
      eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ apply smonoR_Excl. eapply meta_sImp_trans. exact H7.
           eapply sMP.
          ** eapply sMP.
            --- apply sAx ; eapply A8 ; reflexivity.
            --- apply sAx ; eapply A6 ; reflexivity.
          ** eapply meta_sImp_trans. 2: exact H12.
             apply sAx ; eapply A7 ; reflexivity.
      -- eapply meta_sImp_trans.
        ++ eapply meta_sImp_trans.
          ** apply smonoL_Excl. rewrite equiprov in H9. apply H9. auto.
          ** apply smonoR_Excl. eapply meta_sImp_trans. exact H7.
             apply sAx ; eapply A7 ; reflexivity.
        ++ apply sdual_residuation ; auto.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
    destruct HA as (C & D & H0 & H1 & H2 & H3). 
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    unfold sfsubtr in * ; cbn in *. unfold setform in *.
    rewrite H. cbn in * ; unfold sfmeet in * ; cbn in *. unfold setform in *.
    exists (E ∧ (F ∨ D)), F ; repeat split ; auto.
    * exists E, (F ∨ D) ; repeat split ; auto. 2-3: apply simp_Id_gen.
      exists F, D ; repeat split ; auto ; apply simp_Id_gen.
    * eapply meta_sImp_trans. 2: exact H2.
      eapply sMP.
      -- eapply sMP.
        ++ apply sAx ; eapply A8 ; reflexivity.
        ++ eapply meta_sImp_trans. 2: exact H6.
           apply smonoR_Excl. apply sAx ; eapply A6 ; reflexivity.
      -- apply sdual_residuation. apply sAx ; eapply A7 ; reflexivity.
    * eapply meta_sImp_trans. exact H3.
      eapply meta_sImp_trans. apply sAx ; eapply A6 ; reflexivity.
      eapply meta_sImp_trans. exact H7. apply smonoR_Excl.
      assert (H8: @setform Γ (epmeet Γ Φ (epjoin Γ Ψ Χ)) (E ∧ (F ∨ D))).
      { exists E, (F ∨ D) ; repeat split ; auto. 2-3: apply simp_Id_gen.
        exists F, D ; repeat split ; auto ; apply simp_Id_gen. }
      rewrite <- H in H8. rewrite equiprov in H8. apply H8. auto. 
Qed.

End Properties_eqprv.




Section Lindenbaum_algebra.

Variable Γ : @Ensemble form.
Variable Hypirrel : forall Φ Ψ, (@setform Γ Φ = @setform Γ Ψ) -> Φ = Ψ. 

    Instance LindAlg : biHalg :=
      {|
        nodes := eqprv Γ ;

        join := epjoin Γ ;
        meet := epmeet Γ ;
        zero := epzero Γ ;
        one := epone Γ ;
        rpc := eprpc Γ ;
        subtr := epsubtr Γ ;

        jcomm Φ Ψ := epjcomm Γ Hypirrel Φ Ψ ;
        jassoc Φ Ψ Χ := epjassoc Γ Hypirrel Φ Ψ Χ ;
        jabsorp Φ Ψ := epjabsorp Γ Hypirrel Φ Ψ ;
        mcomm Φ Ψ := epmcomm Γ Hypirrel Φ Ψ ;
        massoc Φ Ψ Χ := epmassoc Γ Hypirrel Φ Ψ Χ ;
        mabsorp Φ Ψ := epmabsorp Γ Hypirrel Φ Ψ ;
        lowest Φ := eplowest Γ Hypirrel Φ ;
        greatest Φ := epgreatest Γ Hypirrel Φ ;
        residuation Φ Ψ Χ := epresiduation Γ Hypirrel Φ Ψ Χ ;
        dresiduation Φ Ψ Χ := epdresiduation Γ Hypirrel Φ Ψ Χ
      |}.

    Definition LindAlgamap (n : nat) := @epform_eqprv Γ (# n).

    Lemma LindAlgrepres ϕ : interp LindAlg LindAlgamap ϕ = @epform_eqprv Γ ϕ.
    Proof.
    induction ϕ ; cbn ; auto ; apply Hypirrel ; apply Extensionality_Ensembles ; split ; intros A HA ;
    unfold In in * ; unfold setform in * ; cbn in *.
    (* ⊥ *)
    - split ; auto. apply sEFQ.
    - destruct HA ; auto.
    (* ⊤ *)
    - split.
      + eapply sMP. apply sThm_irrel. exact HA.
      + eapply sMP. apply sThm_irrel. apply sBIH_extens_wBIH ; apply prv_Top.
    - destruct HA. eapply sMP. exact H. apply sBIH_extens_wBIH ; apply prv_Top.
    (* ∧ *)
    - rewrite IHϕ1,IHϕ2 in HA. split.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_sImp_trans. 2: exact H2.
        eapply sMP.
        * eapply sMP.
          -- apply sAx ; eapply A8 ; reflexivity.
          -- eapply meta_sImp_trans.
            ++ apply sAx ; eapply A6 ; reflexivity.
            ++ rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
        * eapply meta_sImp_trans.
          -- apply sAx ; eapply A7 ; reflexivity.
          -- rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_sImp_trans. exact H3.
        eapply sMP.
        * eapply sMP.
          -- apply sAx ; eapply A8 ; reflexivity.
          -- eapply meta_sImp_trans.
            ++ apply sAx ; eapply A6 ; reflexivity.
            ++ rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
        * eapply meta_sImp_trans.
          -- apply sAx ; eapply A7 ; reflexivity.
          -- rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
    - rewrite IHϕ1,IHϕ2. exists ϕ1,ϕ2 ; repeat split ; auto ; try apply simp_Id_gen.
      1-2: destruct HA ; auto.
    (* ∨ *)
    - rewrite IHϕ1,IHϕ2 in HA. split.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_sImp_trans. 2: exact H2.
        eapply sMP.
        * eapply sMP.
          -- apply sAx ; eapply A5 ; reflexivity.
          -- eapply meta_sImp_trans.
            ++ rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
            ++ apply sAx ; eapply A3 ; reflexivity.
        * eapply meta_sImp_trans.
          -- rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
          -- apply sAx ; eapply A4 ; reflexivity.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_sImp_trans. exact H3.
        eapply sMP.
        * eapply sMP.
          -- apply sAx ; eapply A5 ; reflexivity.
          -- eapply meta_sImp_trans.
            ++ rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
            ++ apply sAx ; eapply A3 ; reflexivity.
        * eapply meta_sImp_trans.
          -- rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
          -- apply sAx ; eapply A4 ; reflexivity.
    - rewrite IHϕ1,IHϕ2. exists ϕ1,ϕ2 ; repeat split ; auto ; try apply simp_Id_gen.
      1-2: destruct HA ; auto.
    (* --> *)
    - rewrite IHϕ1,IHϕ2 in HA. split.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_sImp_trans. 2: exact H2.
        eapply sMP. apply sAnd_Imp. eapply meta_sImp_trans.
        * eapply meta_sImp_trans.
          -- eapply sMP.
            ++ eapply sMP.
              ** apply sAx ; eapply A8 ; reflexivity.
              ** apply sAx ; eapply A6 ; reflexivity.
            ++ eapply meta_sImp_trans.
              ** apply sAx ; eapply A7 ; reflexivity.
              ** rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
          -- eapply sMP. apply sImp_And. apply simp_Id_gen.
        * rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_sImp_trans. exact H3.
        eapply sMP. apply sAnd_Imp. eapply meta_sImp_trans.
        * eapply meta_sImp_trans.
          -- eapply sMP.
            ++ eapply sMP.
              ** apply sAx ; eapply A8 ; reflexivity.
              ** apply sAx ; eapply A6 ; reflexivity.
            ++ eapply meta_sImp_trans.
              ** apply sAx ; eapply A7 ; reflexivity.
              ** rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
          -- eapply sMP. apply sImp_And. apply simp_Id_gen.
        * rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
    - rewrite IHϕ1,IHϕ2. exists ϕ1,ϕ2 ; repeat split ; auto ; try apply simp_Id_gen.
      1-2: destruct HA ; auto.
    (* --< *)
    - rewrite IHϕ1,IHϕ2 in HA. split.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_sImp_trans. 2: exact H2.
        eapply meta_sImp_trans.
        * apply smonoL_Excl. rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
        * apply smonoR_Excl. rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_sImp_trans. exact H3.
        eapply meta_sImp_trans.
        * apply smonoL_Excl. rewrite equiprov in H1. destruct (H1 ϕ2).
          -- apply in_sfform_eqprv.
          -- exact H.
        * apply smonoR_Excl. rewrite equiprov in H0. destruct (H0 ϕ1).
          -- apply in_sfform_eqprv.
          -- auto.
    - rewrite IHϕ1,IHϕ2. exists ϕ1,ϕ2 ; repeat split ; auto ; try apply simp_Id_gen.
      1-2: destruct HA ; auto.
    Qed.

End Lindenbaum_algebra.



Section Completeness.

Definition sEq ϕ ψ := ϕ = # 0 /\ ψ = ⊤.

Variable Γ : @Ensemble form.
Variable Hypirrel : forall Φ Ψ, (@setform Γ Φ = @setform Γ Ψ) -> Φ = Ψ. 

Theorem alg_completeness_sBIH ϕ : alg_eqconseq sEq Γ ϕ -> sBIH_prv Γ ϕ.
Proof.
intro H.
epose (LEM _) ; destruct o as [P | NP]; [ exact P | ]. exfalso.
assert (K: sEq # 0 ⊤). split ; auto.
pose (H _ _ K (LindAlg Γ Hypirrel) (LindAlgamap Γ)). cbn in e.
rewrite LindAlgrepres in *.
assert (epform_eqprv Γ ϕ = epone Γ).
{ 
  apply e. intros χ δ H0.
  destruct H0 as (C & D & H1 & E & H3 & H4 & H5) ; subst. inversion H1 ; subst.
  cbn. rewrite LindAlgrepres.
  apply Hypirrel ; apply Extensionality_Ensembles ; split ; intros A HA ; unfold In in * ;
  unfold setform in * ; cbn in *.
  - destruct HA. eapply sMP.
    + exact H0.
    + apply sId ; auto.
  - split.
    + eapply sMP. apply sThm_irrel. auto.
    + eapply sMP. apply sThm_irrel. apply sId ; auto.
}
assert (@setform _ (epone Γ) ϕ).
{
  rewrite <- H0. apply in_sfform_eqprv.
}
auto.
Qed.

End Completeness.

