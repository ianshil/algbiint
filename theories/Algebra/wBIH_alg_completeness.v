Require Import Ensembles.
Require Import List.

Require Import Syntax.
Require Import Bi_Heyting_Algebras.
Require Import algebraic_semantic.
Require Import BIH_export.

Axiom LEM : forall P, P \/ ~ P.

Section Equiprovable_classes. 

Class eqprv : Type :=
  { setform : @Ensemble form ;
    equiprov ϕ : setform ϕ <-> (forall ψ, setform ψ ->
                   (wBIH_prv (Empty_set _) (ϕ --> ψ) /\
                    wBIH_prv (Empty_set _) (ψ --> ϕ)))
  }.

Lemma inhab_eqprv (Φ : eqprv) : exists ϕ, (@setform Φ) ϕ.
Proof.
epose (LEM _) ; destruct o as [P | NP] ; [ exact P | exfalso].
destruct (equiprov ⊤). apply NP. exists ⊤. apply H0.
intros. exfalso. apply NP ; exists ψ ; auto.
Qed.

(* Equiprovable classes. *)

Definition sfform_eqprv ϕ := fun ψ => wBIH_prv (Empty_set _) (ϕ --> ψ) /\
                                      wBIH_prv (Empty_set _) (ψ --> ϕ).

Lemma in_sfform_eqprv ϕ : sfform_eqprv ϕ ϕ.
Proof.
split ; apply imp_Id_gen.
Qed.

Lemma eprvform_eqprv ϕ : forall χ, sfform_eqprv ϕ χ <-> (forall ψ, sfform_eqprv ϕ ψ ->
                   (wBIH_prv (Empty_set _) (χ --> ψ) /\
                    wBIH_prv (Empty_set _) (ψ --> χ))).
Proof.
intros χ ; split ; intro H.
- intros ψ Hψ ; split ; unfold sfform_eqprv in * ; destruct H ; destruct Hψ.
  + eapply meta_Imp_trans. exact H0. auto.  
  + eapply meta_Imp_trans. exact H2. auto.
- split ; apply H ; split ; apply imp_Id_gen.
Qed.

Instance  epform_eqprv ϕ : eqprv :=
    {| 
        setform := sfform_eqprv ϕ ;
        equiprov := eprvform_eqprv ϕ
    |}.

Definition sfone := fun ϕ => wBIH_prv (Empty_set _) ϕ.

Lemma eprvone : forall ϕ, sfone ϕ <-> (forall ψ, sfone ψ ->
                   (wBIH_prv (Empty_set _) (ϕ --> ψ) /\
                    wBIH_prv (Empty_set _) (ψ --> ϕ))).
Proof.
intros ϕ ; split ; intro H.
- intros ψ Hψ ; split. 
  + eapply wMP. apply Thm_irrel. auto.
  + eapply wMP. apply Thm_irrel. auto.
- destruct (H ⊤).
  + apply prv_Top.
  + eapply wMP. 2: apply prv_Top. auto.
Qed.

Instance  epone : eqprv :=
    {| 
        setform := sfone ;
        equiprov := eprvone
    |}.

(* Equiprovable class of ⊥. *)

Definition sfzero := fun ϕ => wBIH_prv (Empty_set _) (ϕ --> ⊥).

Lemma eprvzero : forall ϕ, sfzero ϕ <-> (forall ψ, sfzero ψ ->
                   (wBIH_prv (Empty_set _) (ϕ --> ψ) /\
                    wBIH_prv (Empty_set _) (ψ --> ϕ))).
Proof.
intros ϕ ; split ; intro H.
- intros ψ Hψ ; split. 
  + eapply meta_Imp_trans. 2: apply EFQ. auto.
  + eapply meta_Imp_trans. 2: apply EFQ. auto.
- destruct (H ⊥) ; auto. apply imp_Id_gen.
Qed.

Instance  epzero : eqprv :=
    {| 
        setform := sfzero ;
        equiprov := eprvzero
    |}.

(* Join of equivalence classes. *)

Definition sfjoin (Φ Ψ : eqprv) := fun χ => exists ϕ ψ,
    (@setform Φ) ϕ /\ (@setform Ψ) ψ /\
    wBIH_prv (Empty_set _) ((ϕ ∨ ψ) --> χ) /\ wBIH_prv (Empty_set _) (χ --> (ϕ ∨ ψ)).

Lemma eprvjoin Φ Ψ : forall ϕ, (sfjoin Φ Ψ) ϕ <-> (forall ψ, (sfjoin Φ Ψ) ψ ->
                   (wBIH_prv (Empty_set _) (ϕ --> ψ) /\
                    wBIH_prv (Empty_set _) (ψ --> ϕ))).
Proof.
intros χ ; split ; intro H.
- intros δ Hδ ; split. 
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply meta_Imp_trans ; [exact H7 | ].
    eapply meta_Imp_trans ; [ | exact H2]. eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A5 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ rewrite (@equiprov Φ) in H0 ; apply H0 ; auto.
        ++ apply wAx ; eapply A3 ; reflexivity.
    * eapply meta_Imp_trans.
      -- rewrite (@equiprov Ψ) in H1 ; apply H1 ; auto.
      -- apply wAx ; eapply A4 ; reflexivity.
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply meta_Imp_trans ; [exact H3 | ].
    eapply meta_Imp_trans ; [ | exact H6]. eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A5 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ rewrite (@equiprov Φ) in H4 ; apply H4 ; auto.
        ++ apply wAx ; eapply A3 ; reflexivity.
    * eapply meta_Imp_trans.
      -- rewrite (@equiprov Ψ) in H5 ; apply H5 ; auto.
      -- apply wAx ; eapply A4 ; reflexivity.
- destruct (inhab_eqprv Φ) as (ϕ & H1) ; destruct (inhab_eqprv Ψ) as (ψ & H2).
  exists ϕ, ψ ; repeat split ; auto.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply imp_Id_gen.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply imp_Id_gen.
Qed.

Instance  epjoin Φ Ψ: eqprv :=
    {| 
        setform := sfjoin Φ Ψ ;
        equiprov := eprvjoin Φ Ψ
    |}.

(* Meet of equivalence classes. *)

Definition sfmeet (Φ Ψ : eqprv) := fun χ => exists ϕ ψ,
    (@setform Φ) ϕ /\ (@setform Ψ) ψ /\
    wBIH_prv (Empty_set _) ((ϕ ∧ ψ) --> χ) /\ wBIH_prv (Empty_set _) (χ --> (ϕ ∧ ψ)).

Lemma eprvmeet Φ Ψ : forall ϕ, (sfmeet Φ Ψ) ϕ <-> (forall ψ, (sfmeet Φ Ψ) ψ ->
                   (wBIH_prv (Empty_set _) (ϕ --> ψ) /\
                    wBIH_prv (Empty_set _) (ψ --> ϕ))).
Proof.
intros χ ; split ; intro H.
- intros δ Hδ ; split. 
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply meta_Imp_trans ; [exact H7 | ].
    eapply meta_Imp_trans ; [ | exact H2]. eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ apply wAx ; eapply A6 ; reflexivity.
        ++ rewrite (@equiprov Φ) in H0 ; apply H0 ; auto.
    * eapply meta_Imp_trans.
      -- apply wAx ; eapply A7 ; reflexivity.
      -- rewrite (@equiprov Ψ) in H1 ; apply H1 ; auto.
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply meta_Imp_trans ; [exact H3 | ].
    eapply meta_Imp_trans ; [ | exact H6]. eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ apply wAx ; eapply A6 ; reflexivity.
        ++ rewrite (@equiprov Φ) in H4 ; apply H4 ; auto.
    * eapply meta_Imp_trans.
      -- apply wAx ; eapply A7 ; reflexivity.
      -- rewrite (@equiprov Ψ) in H5 ; apply H5 ; auto.
- destruct (inhab_eqprv Φ) as (ϕ & H1) ; destruct (inhab_eqprv Ψ) as (ψ & H2).
  exists ϕ, ψ ; repeat split ; auto.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply imp_Id_gen.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply imp_Id_gen.
Qed.

Instance  epmeet Φ Ψ: eqprv :=
    {| 
        setform := sfmeet Φ Ψ ;
        equiprov := eprvmeet Φ Ψ
    |}.

(* Implication of equivalence classes. *)

Definition sfrpc (Φ Ψ : eqprv) := fun χ => exists ϕ ψ,
    (@setform Φ) ϕ /\ (@setform Ψ) ψ /\
    wBIH_prv (Empty_set _) ((ϕ --> ψ) --> χ) /\ wBIH_prv (Empty_set _) (χ --> (ϕ --> ψ)).

Lemma eprvrpc Φ Ψ : forall ϕ, (sfrpc Φ Ψ) ϕ <-> (forall ψ, (sfrpc Φ Ψ) ψ ->
                   (wBIH_prv (Empty_set _) (ϕ --> ψ) /\
                    wBIH_prv (Empty_set _) (ψ --> ϕ))).
Proof.
intros χ ; split ; intro H.
- intros δ Hδ ; split. 
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply meta_Imp_trans ; [exact H7 | ].
    eapply meta_Imp_trans ; [ | exact H2]. eapply wMP ; [apply And_Imp | ].
    eapply meta_Imp_trans ; [ | rewrite (@equiprov Ψ) in H5 ; apply H5 ; auto ].
    eapply meta_Imp_trans ; [ | eapply wMP ; [ apply Imp_And | apply imp_Id_gen]].
    eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- apply wAx ; eapply A6 ; reflexivity.
    * eapply meta_Imp_trans.
      -- apply wAx ; eapply A7 ; reflexivity.
      --rewrite (@equiprov Φ) in H0 ; apply H0 ; auto.
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply meta_Imp_trans ; [exact H3 | ].
    eapply meta_Imp_trans ; [ | exact H6]. eapply wMP ; [apply And_Imp | ].
    eapply meta_Imp_trans ; [ | rewrite (@equiprov Ψ) in H1 ; apply H1 ; auto ].
    eapply meta_Imp_trans ; [ | eapply wMP ; [ apply Imp_And | apply imp_Id_gen]].
    eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- apply wAx ; eapply A6 ; reflexivity.
    * eapply meta_Imp_trans.
      -- apply wAx ; eapply A7 ; reflexivity.
      --rewrite (@equiprov Φ) in H4 ; apply H4 ; auto.
- destruct (inhab_eqprv Φ) as (ϕ & H1) ; destruct (inhab_eqprv Ψ) as (ψ & H2).
  exists ϕ, ψ ; repeat split ; auto.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply imp_Id_gen.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply imp_Id_gen.
Qed.

Instance  eprpc Φ Ψ: eqprv :=
    {| 
        setform := sfrpc Φ Ψ ;
        equiprov := eprvrpc Φ Ψ
    |}.

Definition sfsubtr (Φ Ψ : eqprv) := fun χ => exists ϕ ψ,
    (@setform Φ) ϕ /\ (@setform Ψ) ψ /\
    wBIH_prv (Empty_set _) ((ϕ --< ψ) --> χ) /\ wBIH_prv (Empty_set _) (χ --> (ϕ --< ψ)).

Lemma eprvsubtr Φ Ψ : forall ϕ, (sfsubtr Φ Ψ) ϕ <-> (forall ψ, (sfsubtr Φ Ψ) ψ ->
                   (wBIH_prv (Empty_set _) (ϕ --> ψ) /\
                    wBIH_prv (Empty_set _) (ψ --> ϕ))).
Proof.
intros χ ; split ; intro H.
- intros δ Hδ ; split. 
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply meta_Imp_trans ; [exact H7 | ].
    eapply meta_Imp_trans ; [ | exact H2].
    eapply meta_Imp_trans.
    * apply monoL_Excl ; rewrite (@equiprov Ψ) in H1 ; apply H1 ; auto.
    * apply monoR_Excl ; rewrite (@equiprov Φ) in H0 ; apply H0 ; exact H4.
  + destruct Hδ as (ϕ0 & ψ0 & H0 & H1 & H2 & H3).
    destruct H as (ϕ1 & ψ1 & H4 & H5 & H6 & H7).
    eapply meta_Imp_trans ; [exact H3 | ].
    eapply meta_Imp_trans ; [ | exact H6].
    eapply meta_Imp_trans.
    * apply monoL_Excl ; rewrite (@equiprov Ψ) in H5 ; apply H5 ; auto.
    * apply monoR_Excl ; rewrite (@equiprov Φ) in H4 ; apply H4 ; auto.
- destruct (inhab_eqprv Φ) as (ϕ & H1) ; destruct (inhab_eqprv Ψ) as (ψ & H2).
  exists ϕ, ψ ; repeat split ; auto.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply imp_Id_gen.
  + apply H. exists ϕ,ψ ; repeat split ; auto ; apply imp_Id_gen.
Qed.

Instance  epsubtr Φ Ψ: eqprv :=
    {| 
        setform := sfsubtr Φ Ψ ;
        equiprov := eprvsubtr Φ Ψ
    |}.

End Equiprovable_classes.







Section Properties_eqprv.

Variable eqprv_prf_irrel : forall Φ Ψ, (@setform Φ = @setform Ψ) -> Φ = Ψ. 

Lemma epjcomm Φ Ψ : epjoin Φ Ψ = epjoin Ψ Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). exists D,C ; repeat split ; auto.
  + eapply meta_Imp_trans ; [ apply comm_Or_obj | exact H2].
  + eapply meta_Imp_trans ; [exact H3 | apply comm_Or_obj].
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). exists D,C ; repeat split ; auto.
  + eapply meta_Imp_trans ; [ apply comm_Or_obj | exact H2].
  + eapply meta_Imp_trans ; [exact H3 | apply comm_Or_obj].
Qed.

Lemma epjassoc Φ Ψ Χ : epjoin Φ (epjoin Ψ Χ) = epjoin (epjoin Φ Ψ) Χ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3).
  unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn in *.
  destruct H1 as (E & F & H4 & H5 & H6 & H7). unfold setform in *.
  exists (C ∨ E), F ; repeat split ; auto.
  + exists C, E ; repeat split ; auto ; apply imp_Id_gen.
  + eapply meta_Imp_trans ; [apply Or_imp_assoc ; apply imp_Id_gen | ].
    eapply meta_Imp_trans ; [ | exact H2].
    apply monotL_Or ; auto.
  + eapply meta_Imp_trans ; [exact H3 | ].
    eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A5 ; reflexivity.
      -- eapply meta_Imp_trans ; (apply wAx ; eapply A3 ; reflexivity).
    * eapply meta_Imp_trans ; [ exact H7 | ].
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A5 ; reflexivity.
        ++ eapply meta_Imp_trans ; [apply wAx ; eapply A4 ; reflexivity | apply wAx ; eapply A3 ; reflexivity].
      -- apply wAx ; eapply A4 ; reflexivity.
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3).
  unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn in *.
  destruct H0 as (E & F & H4 & H5 & H6 & H7). unfold setform in *.
  exists E, (F ∨ D) ; repeat split ; auto.
  + exists F, D ; repeat split ; auto ; apply imp_Id_gen.
  + eapply meta_Imp_trans ; [ | exact H2].
    eapply meta_Imp_trans ; [ | apply monotR_Or ; exact H6].
    eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A5 ; reflexivity.
      -- eapply meta_Imp_trans ; (apply wAx ; eapply A3 ; reflexivity).
    * eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A5 ; reflexivity.
        ++ eapply meta_Imp_trans ; [apply wAx ; eapply A4 ; reflexivity | apply wAx ; eapply A3 ; reflexivity].
      -- apply wAx ; eapply A4 ; reflexivity.
  + eapply meta_Imp_trans ; [ | apply Or_imp_assoc ; apply imp_Id_gen].
    eapply meta_Imp_trans ; [exact H3 | ].
    apply monotR_Or ; auto.
Qed.

Lemma epjabsorp Φ Ψ : epjoin Φ (epmeet Φ Ψ) = Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). 
  cbn in * ; unfold sfmeet in * ; cbn.
  destruct H1 as (E & F & H4 & H5 & H6 & H7).
  apply equiprov. intros B HB. split.
  + eapply meta_Imp_trans ; [exact H3 | ].
    eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A5 ; reflexivity.
      -- rewrite equiprov in HB. apply HB. exact H0.
    * eapply meta_Imp_trans ; [exact H7 | ].
      eapply meta_Imp_trans ; [apply wAx ; eapply A6 ; reflexivity | rewrite equiprov in HB ; apply HB ; auto].
  + eapply meta_Imp_trans ; [ | exact H2].
    eapply meta_Imp_trans ; [rewrite equiprov in H0 ; apply H0 ; auto | apply wAx ; eapply A3 ; reflexivity].
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn ;
  unfold sfmeet in * ; cbn in * ; unfold setform in * ; cbn in *.
  destruct (inhab_eqprv Ψ) as (B & HB).
  exists A, (A ∧ B) ; repeat split ; auto.
  + exists A, B ; repeat split ; auto ; apply imp_Id_gen.
  + eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A5 ; reflexivity.
      -- apply imp_Id_gen.
    * apply wAx ; eapply A6 ; reflexivity.
  + apply wAx ; eapply A3 ; reflexivity.
Qed.

Lemma epmcomm Φ Ψ : epmeet Φ Ψ = epmeet Ψ Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). exists D,C ; repeat split ; auto.
  + eapply meta_Imp_trans ; [apply comm_And_obj | exact H2].
  + eapply meta_Imp_trans ; [exact H3 | apply comm_And_obj].
- unfold In in *. unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). exists D,C ; repeat split ; auto.
  + eapply meta_Imp_trans ; [apply comm_And_obj | exact H2].
  + eapply meta_Imp_trans ; [exact H3 | apply comm_And_obj].
Qed.

Lemma epmassoc Φ Ψ Χ : epmeet Φ (epmeet Ψ Χ) = epmeet (epmeet Φ Ψ) Χ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3).
  unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn in *.
  destruct H1 as (E & F & H4 & H5 & H6 & H7). unfold setform in *.
  exists (C ∧ E), F ; repeat split ; auto.
  + exists C, E ; repeat split ; auto ; apply imp_Id_gen.
  + eapply meta_Imp_trans.
    * apply assoc_And_obj.
    * eapply meta_Imp_trans.
      -- eapply wMP.
        ++ eapply wMP.
          ** apply wAx ; eapply A8 ; reflexivity.
          ** apply wAx ; eapply A6 ; reflexivity.
        ++ eapply meta_Imp_trans.
          ** apply wAx ; eapply A7 ; reflexivity.
          ** exact H6.
      -- auto.
  + eapply meta_Imp_trans.
    * exact H3.
    * eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A8 ; reflexivity.
            --- apply wAx ; eapply A6 ; reflexivity.
          ** eapply meta_Imp_trans.
            --- apply wAx ; eapply A7 ; reflexivity.
            --- eapply meta_Imp_trans.
              +++ exact H7.
              +++ apply wAx ; eapply A6 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ apply wAx ; eapply A7 ; reflexivity.
        ++ eapply meta_Imp_trans.
          ** exact H7.
          ** apply wAx ; eapply A7 ; reflexivity.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3).
  unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn in *.
  destruct H0 as (E & F & H4 & H5 & H6 & H7). unfold setform in *.
  exists E, (F ∧ D) ; repeat split ; auto.
  + exists F, D ; repeat split ; auto ; apply imp_Id_gen.
  + eapply meta_Imp_trans.
    * apply assoc_And_obj.
    * eapply meta_Imp_trans.
      -- eapply wMP.
        ++ eapply wMP.
          ** apply wAx ; eapply A8 ; reflexivity.
          ** eapply meta_Imp_trans.
            --- apply wAx ; eapply A6 ; reflexivity.
            --- exact H6.
        ++ apply wAx ; eapply A7 ; reflexivity.
      -- auto.
  + eapply meta_Imp_trans.
    * exact H3.
    * eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ eapply meta_Imp_trans.
          ** apply wAx ; eapply A6 ; reflexivity.
          ** eapply meta_Imp_trans.
            --- exact H7.
            --- apply wAx ; eapply A6 ; reflexivity.
      -- eapply wMP.
        ++ eapply wMP.
          ** apply wAx ; eapply A8 ; reflexivity.
          ** eapply meta_Imp_trans.
            --- apply wAx ; eapply A6 ; reflexivity.
            --- eapply meta_Imp_trans.
              +++ exact H7.
              +++ apply wAx ; eapply A7 ; reflexivity.
        ++ apply wAx ; eapply A7 ; reflexivity.
Qed.

Lemma epmabsorp Φ Ψ : epmeet Φ (epjoin Φ Ψ) = Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). 
  unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct H1 as (E & F & H4 & H5 & H6 & H7).
  apply equiprov. intros B HB. split.
  + eapply meta_Imp_trans. exact H3.
    eapply meta_Imp_trans.
    * apply wAx ; eapply A6 ; reflexivity.
    * rewrite equiprov in HB. apply HB. auto.
  + eapply meta_Imp_trans. 2: exact H2.
    eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- rewrite equiprov in HB. apply HB. auto.
    * eapply meta_Imp_trans. 2: exact H6.
      eapply meta_Imp_trans.
      -- rewrite equiprov in H4. apply H4. auto.
      -- apply wAx ; eapply A3 ; reflexivity.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn ;
  unfold sfjoin in * ; cbn in * ; unfold setform in * ; cbn in *.
  destruct (inhab_eqprv Ψ) as (B & HB).
  exists A, (A ∨ B) ; repeat split ; auto.
  + exists A, B ; repeat split ; auto ; apply imp_Id_gen.
  + apply wAx ; eapply A6 ; reflexivity.
  + eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- apply imp_Id_gen.
    * apply wAx ; eapply A3 ; reflexivity.
Qed.

Lemma eplowest Φ : epjoin Φ epzero = Φ.
Proof.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; cbn in * ; unfold sfjoin in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). 
  cbn in * ; unfold sfzero in * ; cbn.
  apply equiprov. intros B HB. split.
  + eapply meta_Imp_trans. exact H3.
    eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A5 ; reflexivity.
      -- rewrite equiprov in HB. apply HB. auto.
    * eapply meta_Imp_trans. exact H1. apply EFQ.
  + eapply meta_Imp_trans. 2: exact H2.
    eapply meta_Imp_trans.
    * rewrite equiprov in H0. apply H0. auto.
    * apply wAx ; eapply A3 ; reflexivity.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfjoin in * ; cbn ;
  unfold sfzero in * ; cbn in * ; unfold setform in * ; cbn in *.
  exists A, ⊥ ; repeat split ; auto.
  + apply imp_Id_gen.
  + eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A5 ; reflexivity.
      -- apply imp_Id_gen.
    * apply EFQ.
  + apply wAx ; eapply A3 ; reflexivity.
Qed.

Lemma epgreatest Φ : epmeet Φ epone = Φ.
apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
  destruct HA as (C & D & H0 & H1 & H2 & H3). 
  unfold setform in * ; cbn in * ; unfold sfone in * ; cbn.
  apply equiprov. intros B HB. split.
  + eapply meta_Imp_trans. exact H3.
    eapply meta_Imp_trans.
    * apply wAx ; eapply A6 ; reflexivity.
    * rewrite equiprov in HB. apply HB. exact H0.
  + eapply meta_Imp_trans. 2: exact H2.
    eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- rewrite equiprov in HB. apply HB. auto.
    * eapply wMP. 2: exact H1. apply Thm_irrel.
- unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn ;
  unfold sfone in * ; cbn in * ; unfold setform in * ; cbn in *.
  exists A, ⊤ ; repeat split ; auto.
  + apply prv_Top.
  + apply wAx ; eapply A6 ; reflexivity.
  + eapply wMP.
    * eapply wMP.
      -- apply wAx ; eapply A8 ; reflexivity.
      -- apply imp_Id_gen.
    * eapply wMP. 2: apply prv_Top. apply Thm_irrel.
Qed.

Lemma epresiduation Φ Ψ Χ : (Φ = epmeet Φ (eprpc Ψ Χ)) <-> (epmeet Φ Ψ = epmeet (epmeet Φ Ψ) Χ).
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
    * exists E, G ; repeat split ; auto ; apply imp_Id_gen.
    * eapply meta_Imp_trans. 2: exact H2.
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ eapply meta_Imp_trans. 2: exact H6.
           eapply meta_Imp_trans. apply assoc_And_obj.
           eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A8 ; reflexivity.
            --- apply wAx ; eapply A6 ; reflexivity.
          ** eapply meta_Imp_trans. 2: exact H10.
             eapply meta_Imp_trans. 2: apply Thm_irrel.
             eapply meta_Imp_trans.
            --- apply wAx ; eapply A7 ; reflexivity.
            --- apply wAx ; eapply A7 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ eapply meta_Imp_trans.
          ** apply wAx ; eapply A6 ; reflexivity.
          ** apply wAx ; eapply A7 ; reflexivity.
        ++ rewrite equiprov in H1. apply H1. auto.
    * eapply meta_Imp_trans. exact H3.
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A8 ; reflexivity.
            --- eapply meta_Imp_trans.
              +++ apply wAx ; eapply A6 ; reflexivity.
              +++ eapply meta_Imp_trans. exact H7. apply wAx ; eapply A6 ; reflexivity.
          ** eapply meta_Imp_trans. apply wAx ; eapply A7 ; reflexivity.
             rewrite equiprov in H1. apply H1. auto.
      -- eapply meta_Imp_trans.
        ++ eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A8 ; reflexivity.
            --- eapply meta_Imp_trans.
              +++ apply wAx ; eapply A6 ; reflexivity.
              +++ eapply meta_Imp_trans.
                *** exact H7.
                *** apply wAx ; eapply A7 ; reflexivity.
          ** eapply meta_Imp_trans.
            --- apply wAx ; eapply A7 ; reflexivity.
            --- rewrite equiprov in H8. apply H8. auto.
        ++ eapply wMP.
          ** apply Imp_And.
          ** auto.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn. 
    destruct HA as (C & D & H0 & H1 & H2 & H3).
    cbn in * ; unfold sfmeet in * ; cbn.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    rewrite H. cbn in * ; unfold sfmeet in * ; cbn in *. unfold setform in *.
    exists (E ∧ (F --> D)), F. repeat split ; auto.
    * exists E, (F --> D) ; repeat split ; auto. 2-3: apply imp_Id_gen.
      exists F,D ; repeat split ; auto ; apply imp_Id_gen.
    * eapply meta_Imp_trans. 2: exact H2.
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ eapply meta_Imp_trans. 2: exact H6.
           eapply meta_Imp_trans. apply assoc_And_obj.
           eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A8 ; reflexivity.
            --- apply wAx ; eapply A6 ; reflexivity.
          ** eapply meta_Imp_trans. apply wAx ; eapply A7 ; reflexivity.
             apply wAx ; eapply A7 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A8 ; reflexivity.
            --- eapply meta_Imp_trans.
              +++ apply wAx ; eapply A6 ; reflexivity.
              +++ apply wAx ; eapply A7 ; reflexivity.
          ** apply wAx ; eapply A7 ; reflexivity.
        ++ eapply wMP.
          ** apply Imp_And.
          ** apply imp_Id_gen.
    * eapply meta_Imp_trans. exact H3.
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A8 ; reflexivity.
            --- eapply meta_Imp_trans.
              +++ apply wAx ; eapply A6 ; reflexivity.
              +++ eapply meta_Imp_trans. exact H7. apply wAx ; eapply A6 ; reflexivity.
          ** eapply meta_Imp_trans. apply wAx ; eapply A7 ; reflexivity.
             apply Thm_irrel.
      -- eapply meta_Imp_trans.
        ++ apply wAx ; eapply A6 ; reflexivity.
        ++ eapply meta_Imp_trans.
          ** exact H7.
          ** apply wAx ; eapply A7 ; reflexivity.
- apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
    destruct (inhab_eqprv Ψ) as (B & HB).
    assert (H1: @setform (epmeet Φ Ψ) (A ∧ B)).
    {
      exists A,B ; repeat split ; auto ; apply imp_Id_gen.
    }
    rewrite H in H1. cbn in H1.
    destruct H1 as (C & D & H0 & H1 & H2 & H3). 
    cbn in * ; unfold sfmeet in * ; cbn.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    exists E, (F --> D) ; repeat split ; auto.
    * exists F, D ; repeat split ; auto ; apply imp_Id_gen.
    * eapply meta_Imp_trans.
      -- apply wAx ; eapply A6 ; reflexivity.
      -- rewrite equiprov in H4. apply H4. auto.
    *  eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ rewrite equiprov in H4. apply H4. auto.
      -- eapply wMP.
        ++ apply And_Imp.
        ++ eapply meta_Imp_trans.
          ** eapply meta_Imp_trans.
            --- eapply wMP.
              +++ eapply wMP.
                *** apply wAx ; eapply A8 ; reflexivity.
                *** apply wAx ; eapply A6 ; reflexivity.
              +++ eapply meta_Imp_trans.
                *** apply wAx ; eapply A7 ; reflexivity.
                *** rewrite equiprov in HB. apply HB. auto.
            --- exact H3.
          ** apply wAx ; eapply A7 ; reflexivity.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn. 
    destruct HA as (C & D & H0 & H1 & H2 & H3).
    cbn in * ; unfold sfrpc in * ; cbn.
    destruct H1 as (E & F & H4 & H5 & H6 & H7).
    apply equiprov. intros K HK. split.
    * eapply meta_Imp_trans. exact H3. eapply meta_Imp_trans.
      -- apply wAx ; eapply A6 ; reflexivity.
      -- rewrite equiprov in H0. apply H0. auto.
    * eapply meta_Imp_trans. 2: exact H2.
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ rewrite equiprov in H0. apply H0. auto.
      -- eapply meta_Imp_trans. 2: exact H6.
         eapply wMP.
        ++ apply And_Imp.
        ++ assert (H8: @setform (epmeet Φ Ψ) (K ∧ E)).
           { exists K,E ; repeat split ; auto ; apply imp_Id_gen. }
           rewrite H in H8. unfold setform in H8 ; cbn in H8 ; unfold sfmeet in H8 ; cbn.
           destruct H8 as (J & L & H9 & H10 & H11 & H12).
           eapply meta_Imp_trans.
           ** exact H12.
           ** eapply meta_Imp_trans.
            --- apply wAx ; eapply A7 ; reflexivity.
            --- rewrite equiprov in H10. apply H10. auto.
Qed.

Lemma epdresiduation Φ Ψ Χ : (epsubtr Φ Ψ = epmeet (epsubtr Φ Ψ) Χ) <-> (Φ = epmeet Φ (epjoin Ψ Χ)).
Proof.
split ; intro H.
- apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
    destruct (inhab_eqprv Ψ) as (B & HB).
    assert (H1: @setform (epsubtr Φ Ψ) (A --< B)).
    { exists A,B ; repeat split ; auto ; apply imp_Id_gen. }
    rewrite H in H1. cbn in H1. 
    destruct H1 as (C & D & H0 & H1 & H2 & H3). 
    cbn in * ; unfold sfjoin in * ; cbn.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    exists E, (F ∨ D) ; repeat split ; auto.
    * exists F, D ; repeat split ; auto ; apply imp_Id_gen.
    * eapply meta_Imp_trans.
      -- apply wAx ; eapply A6 ; reflexivity.
      -- rewrite equiprov in H4. apply H4. auto.
    * apply dual_residuation in H3. eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ rewrite equiprov in H4. apply H4. auto.
      -- eapply meta_Imp_trans.
        ++ exact H3.
        ++ eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A5 ; reflexivity.
            --- eapply meta_Imp_trans.
              +++ rewrite equiprov in H5. apply H5. auto.
              +++ apply wAx ; eapply A3 ; reflexivity.
          ** eapply meta_Imp_trans.
            --- apply wAx ; eapply A7 ; reflexivity.
            --- apply wAx ; eapply A4 ; reflexivity.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn. 
    destruct HA as (C & D & H0 & H1 & H2 & H3).
    cbn in * ; unfold sfsubtr in * ; cbn.
    destruct H1 as (E & F & H4 & H5 & H6 & H7).
    apply equiprov. intros K HK. split.
    * eapply meta_Imp_trans. exact H3. eapply meta_Imp_trans.
      -- apply wAx ; eapply A6 ; reflexivity.
      -- rewrite equiprov in H0. apply H0. auto.
    * eapply meta_Imp_trans. 2: exact H2.
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ rewrite equiprov in H0. apply H0. auto.
      -- eapply meta_Imp_trans. 2: exact H6. unfold setform in *.
         apply dual_residuation.
         assert (H8: @setform (epsubtr Φ Ψ) (K --< E)).
         { exists K,E ; repeat split ; auto ; apply imp_Id_gen. }
         rewrite H in H8. unfold setform in H8 ; cbn in H8 ; unfold sfmeet in H8 ; cbn.
         destruct H8 as (J & L & H9 & H10 & H11 & H12).
         eapply meta_Imp_trans.
         ++ exact H12.
         ++ eapply meta_Imp_trans.
          ** apply wAx ; eapply A7 ; reflexivity.
          ** rewrite equiprov in H10. apply H10. auto.
- apply eqprv_prf_irrel. apply Extensionality_Ensembles. split ; intros A HA.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn. 
    destruct HA as (C & D & H0 & H1 & H2 & H3).
    cbn in * ; unfold sfjoin in * ; cbn. rewrite H in H0.
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    destruct H5 as (J & L & H9 & H10 & H11 & H12).
    exists ((E ∧ (J ∨ L)) --< D), L ; repeat split ; auto.
    * exists (E ∧ (J ∨ L)), D ; repeat split ; auto. 2-3: apply imp_Id_gen.
      rewrite H. exists E,(J ∨ L) ; repeat split ; auto. 2-3: apply imp_Id_gen.
      exists J, L ; repeat split ; auto ; apply imp_Id_gen.
    * eapply meta_Imp_trans. 2: exact H2.
      eapply meta_Imp_trans.
      -- apply wAx ; eapply A6 ; reflexivity.
      -- apply monoR_Excl. eapply meta_Imp_trans. 2: exact H6.
         eapply wMP.
        ++ eapply wMP.
          ** apply wAx ; eapply A8 ; reflexivity.
          ** apply wAx ; eapply A6 ; reflexivity.
        ++ eapply meta_Imp_trans. 2: exact H11.
           apply wAx ; eapply A7 ; reflexivity.
    * eapply meta_Imp_trans. exact H3.
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ apply monoR_Excl. eapply meta_Imp_trans. exact H7.
           eapply wMP.
          ** eapply wMP.
            --- apply wAx ; eapply A8 ; reflexivity.
            --- apply wAx ; eapply A6 ; reflexivity.
          ** eapply meta_Imp_trans. 2: exact H12.
             apply wAx ; eapply A7 ; reflexivity.
      -- eapply meta_Imp_trans.
        ++ eapply meta_Imp_trans.
          ** apply monoL_Excl. rewrite equiprov in H9. apply H9. auto.
          ** apply monoR_Excl. eapply meta_Imp_trans. exact H7.
             apply wAx ; eapply A7 ; reflexivity.
        ++ apply dual_residuation ; auto.
  + unfold In in * ; unfold setform in * ; cbn in * ; unfold sfmeet in * ; cbn.
    destruct HA as (C & D & H0 & H1 & H2 & H3). 
    destruct H0 as (E & F & H4 & H5 & H6 & H7).
    unfold sfsubtr in * ; cbn in *. unfold setform in *.
    rewrite H. cbn in * ; unfold sfmeet in * ; cbn in *. unfold setform in *.
    exists (E ∧ (F ∨ D)), F ; repeat split ; auto.
    * exists E, (F ∨ D) ; repeat split ; auto. 2-3: apply imp_Id_gen.
      exists F, D ; repeat split ; auto ; apply imp_Id_gen.
    * eapply meta_Imp_trans. 2: exact H2.
      eapply wMP.
      -- eapply wMP.
        ++ apply wAx ; eapply A8 ; reflexivity.
        ++ eapply meta_Imp_trans. 2: exact H6.
           apply monoR_Excl. apply wAx ; eapply A6 ; reflexivity.
      -- apply dual_residuation. apply wAx ; eapply A7 ; reflexivity.
    * eapply meta_Imp_trans. exact H3.
      eapply meta_Imp_trans. apply wAx ; eapply A6 ; reflexivity.
      eapply meta_Imp_trans. exact H7. apply monoR_Excl.
      assert (H8: @setform (epmeet Φ (epjoin Ψ Χ)) (E ∧ (F ∨ D))).
      { exists E, (F ∨ D) ; repeat split ; auto. 2-3: apply imp_Id_gen.
        exists F, D ; repeat split ; auto ; apply imp_Id_gen. }
      rewrite <- H in H8. rewrite equiprov in H8. apply H8. auto. 
Qed.

End Properties_eqprv.




Section Lindenbaum_algebra.

Variable Hypirrel : forall Φ Ψ, (@setform Φ = @setform Ψ) -> Φ = Ψ. 

    Instance LindAlg : biHalg :=
      {|
        nodes := eqprv ;

        join := epjoin ;
        meet := epmeet ;
        zero := epzero ;
        one := epone ;
        rpc := eprpc ;
        subtr := epsubtr ;

        jcomm Φ Ψ := epjcomm Hypirrel Φ Ψ ;
        jassoc Φ Ψ Χ := epjassoc Hypirrel Φ Ψ Χ ;
        jabsorp Φ Ψ := epjabsorp Hypirrel Φ Ψ ;
        mcomm Φ Ψ := epmcomm Hypirrel Φ Ψ ;
        massoc Φ Ψ Χ := epmassoc Hypirrel Φ Ψ Χ ;
        mabsorp Φ Ψ := epmabsorp Hypirrel Φ Ψ ;
        lowest Φ := eplowest Hypirrel Φ ;
        greatest Φ := epgreatest Hypirrel Φ ;
        residuation Φ Ψ Χ := epresiduation Hypirrel Φ Ψ Χ ;
        dresiduation Φ Ψ Χ := epdresiduation Hypirrel Φ Ψ Χ
      |}.

    Definition LindAlgamap (n : nat) := @epform_eqprv (# n).

    Lemma LindAlgrepres ϕ : interp LindAlg LindAlgamap ϕ = @epform_eqprv ϕ.
    Proof.
    induction ϕ ; cbn ; auto ; apply Hypirrel ; apply Extensionality_Ensembles ; split ; intros A HA ;
    unfold In in * ; unfold setform in * ; cbn in *.
    (* ⊥ *)
    - split ; auto. apply EFQ.
    - destruct HA ; auto.
    (* ⊤ *)
    - split.
      + eapply wMP. apply Thm_irrel. exact HA.
      + eapply wMP. apply Thm_irrel. apply prv_Top.
    - destruct HA. eapply wMP. exact H. apply prv_Top.
    (* ∧ *)
    - rewrite IHϕ1,IHϕ2 in HA. split.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_Imp_trans. 2: exact H2.
        eapply wMP.
        * eapply wMP.
          -- apply wAx ; eapply A8 ; reflexivity.
          -- eapply meta_Imp_trans.
            ++ apply wAx ; eapply A6 ; reflexivity.
            ++ rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
        * eapply meta_Imp_trans.
          -- apply wAx ; eapply A7 ; reflexivity.
          -- rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_Imp_trans. exact H3.
        eapply wMP.
        * eapply wMP.
          -- apply wAx ; eapply A8 ; reflexivity.
          -- eapply meta_Imp_trans.
            ++ apply wAx ; eapply A6 ; reflexivity.
            ++ rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
        * eapply meta_Imp_trans.
          -- apply wAx ; eapply A7 ; reflexivity.
          -- rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
    - rewrite IHϕ1,IHϕ2. exists ϕ1,ϕ2 ; repeat split ; auto ; try apply imp_Id_gen.
      1-2: destruct HA ; auto.
    (* ∨ *)
    - rewrite IHϕ1,IHϕ2 in HA. split.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_Imp_trans. 2: exact H2.
        eapply wMP.
        * eapply wMP.
          -- apply wAx ; eapply A5 ; reflexivity.
          -- eapply meta_Imp_trans.
            ++ rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
            ++ apply wAx ; eapply A3 ; reflexivity.
        * eapply meta_Imp_trans.
          -- rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
          -- apply wAx ; eapply A4 ; reflexivity.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_Imp_trans. exact H3.
        eapply wMP.
        * eapply wMP.
          -- apply wAx ; eapply A5 ; reflexivity.
          -- eapply meta_Imp_trans.
            ++ rewrite equiprov in H0. apply H0 with (ψ:=ϕ1). apply in_sfform_eqprv.
            ++ apply wAx ; eapply A3 ; reflexivity.
        * eapply meta_Imp_trans.
          -- rewrite equiprov in H1. apply H1 with (ψ:=ϕ2). apply in_sfform_eqprv.
          -- apply wAx ; eapply A4 ; reflexivity.
    - rewrite IHϕ1,IHϕ2. exists ϕ1,ϕ2 ; repeat split ; auto ; try apply imp_Id_gen.
      1-2: destruct HA ; auto.
    (* --> *)
    - rewrite IHϕ1,IHϕ2 in HA. split.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_Imp_trans. 2: exact H2.
        eapply wMP. apply And_Imp. eapply meta_Imp_trans.
        * eapply meta_Imp_trans.
          -- eapply wMP.
            ++ eapply wMP.
              ** apply wAx ; eapply A8 ; reflexivity.
              ** apply wAx ; eapply A6 ; reflexivity.
            ++ eapply meta_Imp_trans.
              ** apply wAx ; eapply A7 ; reflexivity.
              ** rewrite equiprov in H0. apply H0 with (ψ:=ϕ1). apply in_sfform_eqprv.
          -- eapply wMP. apply Imp_And. apply imp_Id_gen.
        * rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_Imp_trans. exact H3.
        eapply wMP. apply And_Imp. eapply meta_Imp_trans.
        * eapply meta_Imp_trans.
          -- eapply wMP.
            ++ eapply wMP.
              ** apply wAx ; eapply A8 ; reflexivity.
              ** apply wAx ; eapply A6 ; reflexivity.
            ++ eapply meta_Imp_trans.
              ** apply wAx ; eapply A7 ; reflexivity.
              ** rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
          -- eapply wMP. apply Imp_And. apply imp_Id_gen.
        * rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
    - rewrite IHϕ1,IHϕ2. exists ϕ1,ϕ2 ; repeat split ; auto ; try apply imp_Id_gen.
      1-2: destruct HA ; auto.
    (* --< *)
    - rewrite IHϕ1,IHϕ2 in HA. split.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_Imp_trans. 2: exact H2.
        eapply meta_Imp_trans.
        * apply monoL_Excl. rewrite equiprov in H1. apply H1. apply in_sfform_eqprv.
        * apply monoR_Excl. rewrite equiprov in H0. apply H0. apply in_sfform_eqprv.
      + destruct HA as (B & C & H0 & H1 & H2 & H3). eapply meta_Imp_trans. exact H3.
        eapply meta_Imp_trans.
        * apply monoL_Excl. rewrite equiprov in H1. destruct (H1 ϕ2).
          -- apply in_sfform_eqprv.
          -- exact H4.
        * apply monoR_Excl. rewrite equiprov in H0. destruct (H0 ϕ1).
          -- apply in_sfform_eqprv.
          -- auto.
    - rewrite IHϕ1,IHϕ2. exists ϕ1,ϕ2 ; repeat split ; auto ; try apply imp_Id_gen.
      1-2: destruct HA ; auto.
    Qed.

End Lindenbaum_algebra.



Section Completeness.

Variable Hypirrel : forall Φ Ψ, (@setform Φ = @setform Ψ) -> Φ = Ψ. 

Theorem algtd_completeness_wBIH (Γ: Ensemble _) ϕ : alg_tdconseq Γ ϕ -> wBIH_prv Γ ϕ.
Proof.
intro H. destruct H as (Δ & H0 & (l & H1) & H2).
apply wBIH_monot with Δ ; auto.
apply list_conj_finite_context with l.
- intro B ; split ; intro ; apply H1 ; auto.
- enough (epform_eqprv (list_conj l --> ϕ) = (@one (LindAlg Hypirrel))).
  + assert ((@setform epone) (list_conj l --> ϕ)).
    { unfold setform. unfold one in H ; cbn in H. rewrite <- H.
      apply in_sfform_eqprv. }
    rewrite eprvone in H3.
    apply wBIH_comp with (Union _ (Union _ (Empty_set _) (Singleton _ ⊤)) (Singleton _ (list_conj l))).
    * repeat apply wBIH_Detachment_Theorem. apply H3.
      apply prv_Top.
    * intros. inversion H4 ; subst.
      -- inversion H5 ; subst ; try contradiction.
         inversion H6 ; subst ; apply prv_Top.
      -- apply wId ; auto.
  + apply (aleq_antisym (LindAlg Hypirrel)).
    * apply high_one.
    * pose (LindAlgrepres Hypirrel ((list_conj l) --> ϕ)).
      rewrite <- e. simpl (interp (LindAlg Hypirrel) LindAlgamap (list_conj l --> ϕ)).
      rewrite ord_resid. rewrite mcomm. rewrite greatest.
      apply (H2 (LindAlg Hypirrel) LindAlgamap). intros.
      rewrite list_conj_interp. apply list_meet_all.
      apply in_map_iff. exists γ ; split ; auto. apply H1 ; auto.
Qed.

End Completeness.

