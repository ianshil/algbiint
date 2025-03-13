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
Require Import sBIH_meta_interactions.
Require Import BiInt_Kripke_sem.
Require Import BiInt_soundness.
Require Import wBIH_completeness.
Require Import sBIH_completeness.

Section ConseqSoundness.

Section DefModels.

Inductive UnDeux  : Type :=
 | Un : UnDeux
 | Deux : UnDeux.

Definition UDle (n m : UnDeux) : Prop :=
  match n with
   | Un => True
   | Deux => match m with
                   | Un => False
                   | Deux => True
                  end
  end.

Lemma UDle_refl : forall n, UDle n n.
Proof.
intros. destruct n ; unfold UDle ; auto.
Qed.

Lemma UDle_trans : forall n m k, (UDle n m) -> (UDle m k) -> (UDle n k).
Proof.
intros. destruct n ; unfold UDle ; auto. destruct k ; unfold UDle ; auto.
destruct m ; unfold UDle ; auto.
Qed.

Inductive UnDeuxTrois  : Type :=
 | UnDeux_I : UnDeux -> UnDeuxTrois
 | Trois : UnDeuxTrois.

Definition UDTle (n m : UnDeuxTrois) : Prop :=
  match n with
   | UnDeux_I k => match m with
                            | UnDeux_I l => UDle k l
                            | Trois => False
                           end
   | Trois => match m with
                   | UnDeux_I k => match k with
                                               | Un => False
                                               | Deux => True
                                              end
                   | Trois => True
                  end
  end.

Lemma UDTle_refl : forall n, UDTle n n.
Proof.
intros. destruct n ; unfold UDTle ; auto. apply UDle_refl.
Qed.

Lemma UDTle_trans : forall n m k, (UDTle n m) -> (UDTle m k) -> (UDTle n k).
Proof.
intros. destruct n ; unfold UDTle ; auto. destruct k ; unfold UDTle ; auto.
destruct m ; unfold UDTle ; auto. simpl in H. simpl in H0. apply (UDle_trans _ _ _ H H0) ; auto.
simpl in H0. destruct u0 ; simpl ; auto. inversion H0. simpl in H. inversion H.
destruct m ; auto. destruct k ; simpl ; auto. destruct u ; simpl ; auto.
destruct m ; auto. simpl in H0. simpl in H. destruct u ; auto.
Qed.

Definition val1 (n : UnDeux) (r : nat) :=
  match n with
    | Un => False
    | Deux => True
  end.

Lemma persist_val1 : forall u v, UDle u v -> forall p, val1 u 0 -> val1 v p.
Proof.
intros. destruct u.
- simpl in H0. inversion H0.
- simpl in H0. destruct v.
  + simpl. inversion H.
  + simpl. auto.
Qed.

Instance M0 : model :=
      {|
        nodes := UnDeux ;
        reachable := UDle ;
        val := val1 ;

        reach_refl u := UDle_refl u ;
        reach_tran u v w := @UDle_trans u v w ;

        persist := persist_val1;
      |}.

Definition val2 (n : UnDeuxTrois) (p : nat) :=
  match n with
    | UnDeux_I n => match n with
                                | Un => False
                                | Deux => True
                                end
    | Trois => True
  end.

Lemma persist_val2 : forall u v,
  UDTle u v -> forall p, val2 u 0 -> val2 v p.
Proof.
intros. destruct u.
- destruct u. simpl in H0. inversion H0. simpl in H0.
  destruct v ; auto.
- simpl in H0. destruct v ; simpl ; auto.
Qed.

Instance M2 : model :=
      {|
        nodes := UnDeuxTrois ;
        reachable := UDTle ;
        val := val2 ;

        reach_refl u := UDTle_refl u ;
        reach_tran u v w := @UDTle_trans u v w ;

        persist := persist_val2;
      |}.

Inductive TpFq (r : nat) : Prop :=
 | Fq : ((r = 1) -> False) -> TpFq r.

Definition val3 (n : UnDeuxTrois) (r : nat) :=
  match n with
    | UnDeux_I n => match n with
                                | Un => TpFq r
                                | Deux => True
                                end
    | Trois => True
  end.

Lemma persist_val3 : forall u v,
  UDTle u v -> forall r, val3 u r -> val3 v r.
Proof.
intros. destruct u.
- destruct u.
  + simpl in H0. simpl in H. destruct v.
    * destruct u. simpl. auto. simpl. auto.
    * simpl. auto.
  + simpl in H0. simpl in H. destruct v.
    * destruct u. simpl. inversion H. simpl. auto.
    * simpl. auto.
- simpl in H0. simpl in H. destruct v ; auto.
  destruct u ; auto. inversion H.
Qed.




(* destruct (eq_dec_propvar r p).
  + subst. destruct v ; auto. simpl. destruct u0. split ; auto. apply diff_prop.
     apply Logic.I. simpl. apply Logic.I.
  + destruct (eq_dec_propvar r q).
    * subst. destruct v ; auto. simpl. destruct u0. simpl in H0. destruct u.
      inversion H0. exfalso ; apply H1 ; auto. 2: auto. simpl in H. inversion H.
      simpl. auto.
    * 



  + destruct u. destruct p. simpl in H0. destruct v ; auto. simpl. destruct u ; auto.
     destruct p. simpl in H0. destruct v ; auto. simpl. destruct u ; auto.
  + destruct v ; simpl ; auto. destruct u0 ; auto. simpl in H0. destruct u ; auto.
- destruct PQ1.
  + destruct p. simpl in H0. destruct v ; simpl ; auto. destruct u ; simpl ; auto.
  + simpl in H0. destruct v ; simpl ; auto. destruct u ; simpl ; auto.
Qed. *)

Instance M1 : model :=
      {|
        nodes := UnDeuxTrois ;
        reachable := UDTle ;
        val := val3 ;

        reach_refl u := UDTle_refl u ;
        reach_tran u v w := @UDTle_trans u v w ;

         persist := persist_val3;
      |}.

End DefModels.



Section Counterexamples.

(* sBIL is not a subset of wBIL. *)

Lemma Consequences_Soundness1 :
  sBIH_prv (Singleton _ (# 0)) (¬ ∞ # 0) /\
  ~ wBIH_prv (Singleton _ (# 0)) (¬ ∞ # 0).
Proof.
split.
- apply sDN. apply sId ; split.
- intro. apply LEM_wSoundness in H. pose (H M0 Deux).
  assert (J0: wforces M0 Deux (¬ ∞ # 0)).
  { assert (forall A, (Singleton _ # 0) A -> wforces M0 Deux A).
    intros. inversion H0. subst. simpl. apply Logic.I.
    apply w in H0 ; auto. }
  pose (J0 Deux Logic.I). simpl in w0. apply w0. intro.
  pose (H0 Un). cbn in v. auto.
Qed.

Theorem sBIH_not_incl_wBIH :
   spair_der (Singleton _ (# 0)) (Singleton _ (¬ ∞ # 0)) /\
   ~ wpair_der (Singleton _ (# 0)) (Singleton _ (¬ ∞ # 0)).
Proof.
split. 
- exists [(¬ ∞ # 0)]. repeat split ; auto.
  + apply NoDup_cons ; auto. apply NoDup_nil.
  + intros. inversion H ; subst. split. inversion H0.
  + cbn. eapply sMP. apply sAx ; eapply A3 ; reflexivity.
     apply Consequences_Soundness1.
- intro H. destruct H as (l & H0 & H1 & H2).
  destruct l ; cbn in *.
  + assert (J: wBIH_prv (Empty_set form) ⊥).
     { apply wBIH_comp with (Singleton form Top) ; auto. 
       - apply wBIH_struct with (f:= fun n => Top) in H2.
         cbn in H2. apply (wBIH_monot _ _ H2). intros A (C & HC0 & HC1) ; inversion HC1 ; subst.
         cbn in * ; split.
       - intros. inversion H. apply prv_Top. }
     destruct (LEM_wSoundness (Empty_set _) Bot J M0 Un).
     intros. inversion H.
  + destruct l ; cbn in *.
     * apply absorp_Or1 in H2. destruct (H1 f) ; auto.
       apply Consequences_Soundness1 ; auto.
     * destruct (H1 f) ; auto. destruct (H1 f0) ; auto. inversion H0 ; subst.
       apply H4 ; cbn ; auto.
Qed.

(* Failure of deduction theorem for sBIL *)

Lemma Consequences_Soundness2 :
  sBIH_prv (Singleton _ # 0) (¬ ∞ # 0) /\
  ~ sBIH_prv (Empty_set _)  (# 0 --> ¬ ∞ # 0).
Proof.
split.
- apply sDN. apply sId ; split.
- intro. apply LEM_sSoundness in H.
   assert (J0: (forall A, In _ (Empty_set _) A -> forall u : UnDeux, wforces M0 u  A)).
  { intros. inversion H0. }
  pose (H M0 J0 Deux).
  pose (w Deux Logic.I Logic.I Deux Logic.I). cbn in w0.
  apply w0. intro H2. pose (H2 Un). cbn in v ; auto.
Qed.

Theorem failure_gen_sBIH_Deduction_Theorem : 
  spair_der (Union _ (Empty_set _) (Singleton _ # 0)) (Singleton _ (¬ ∞ # 0)) /\
  ~ spair_der (Empty_set _) (Singleton _ (# 0 --> ¬ ∞ # 0)).
Proof.
split.
- exists [(¬ (∞ (# 0)))].
  repeat split. apply NoDup_cons. intro. inversion H. apply NoDup_nil.
  intros. simpl. inversion H. subst. apply In_singleton. inversion H0.
  simpl. assert (Union _ (Empty_set _) (Singleton _ # 0) = Singleton _ # 0).
  apply Extensionality_Ensembles. unfold Same_set. split. intro. intros.
  inversion H. inversion H0. inversion H0. subst ; auto. intro. intros.
  inversion H. subst. apply Union_intror. auto. rewrite H. pose (extens_diff_sBIH 0).
  eapply sMP. apply sAx ; eapply A3 ; reflexivity. auto.
- intro. destruct H as (l & H0 & H1 & H2).
  apply LEM_sSoundness in H2.
  assert (J1: (forall A, (Empty_set _) A -> mforces M0 A)).
  { intros. inversion H. }
  pose (H2 M0 J1 Deux). destruct l ; cbn in * ; try contradiction.
  destruct l ; cbn in *.
  + destruct w ; try contradiction. destruct (H1 f) ; auto.
    pose (H Deux Logic.I Logic.I Deux I) ; cbn in w.
    apply w. intro. pose (H3 Un). cbn in v ; auto.
  + inversion H0 ; subst. inversion H5 ; subst.
    destruct (H1 f0) ; auto. destruct (H1 f) ; auto.
    apply H4 ; cbn ; auto.
Qed.

(* DMP fails in sBIL. *)

Lemma Consequences_Soundness3 :
  ~ spair_der (Singleton _  # 0) (Union _ (Singleton _  # 1) (Singleton _  (¬ ∞ ∞ # 1))).
Proof.
intro. destruct H as (l & H0 & H1 & H2).
apply LEM_sSoundness in H2.
assert (J0: (forall A, (Singleton _ # 0) A -> mforces M1 A)).
{ intros. inversion H. subst. intro. destruct w ; simpl ; auto.
  destruct u ; simpl ; auto. apply Fq. lia. }
pose (H2 M1 J0 (UnDeux_I Un)). destruct l ; cbn in * ; try contradiction.
destruct l ; cbn in *.
- destruct w ; try contradiction. destruct (H1 f) ; auto.
  + inversion H3 ; subst. cbn in H. inversion H ; auto.
  + inversion H3; subst. cbn in H.
    pose (H (UnDeux_I Deux) Logic.I). apply f.
    intro. pose (H4 Trois). cbn in *. apply n ; auto.
    intros. destruct v ; auto. cbn. destruct u ; cbn in * ; auto.
    contradiction.
- destruct l ; cbn in *.
  + destruct w.
    * destruct (H1 f) ; auto.
      -- inversion H3 ; subst. cbn in H. inversion H ; auto.
      -- inversion H3 ; subst. cbn in H.
         pose (H (UnDeux_I Deux) Logic.I). apply f.
         intro. pose (H4 Trois). cbn in *. apply n ; auto.
         intros. destruct v ; auto. cbn. destruct u ; cbn in * ; auto.
         contradiction.
    * destruct H ; try contradiction. destruct (H1 f0) ; auto.
      -- inversion H3 ; subst. cbn in H. inversion H ; auto.
      -- inversion H3 ; subst. cbn in H.
         pose (H (UnDeux_I Deux) Logic.I). apply f0.
         intro. pose (H4 Trois). cbn in *. apply n ; auto.
         intros. destruct v ; auto. cbn. destruct u ; cbn in * ; auto.
         contradiction.
  + inversion H0 ; subst. inversion H5 ; subst. inversion H7 ; subst.
    apply H4. destruct (H1 f) ; destruct (H1 f0) ; destruct (H1 f1) ; auto ;
    inversion H ; inversion H3 ; inversion H10 ; subst ; cbn ; auto.
    all: exfalso ; apply H6 ; cbn ; auto. 
Qed.

(* Failure dual deduction theorem *)

Theorem failure_gen_sBIH_Dual_Detachment_Theorem :
  spair_der (Singleton _ (# 0 --< # 1)) (Singleton _ (¬ ∞ ∞ # 1)) /\
  ~ spair_der (Singleton _ # 0) (Union _ (Singleton _ # 1) (Singleton _ (¬ ∞ ∞ # 1))).
Proof.
split.
- unfold spair_der. exists [(¬ (∞ (∞ (# 1))))]. repeat split. apply NoDup_cons.
  intro. inversion H. apply NoDup_nil. intros. simpl. inversion H. subst. apply In_singleton.
  inversion H0. simpl.
  eapply sMP. apply sAx ; eapply A3 ; reflexivity.
  apply sDN. apply sBIH_extens_wBIH.
  apply wBIH_monot with (Union _ (Empty_set _) (Singleton form (# 0 --< # 1))).
  apply wBIH_Detachment_Theorem.
  apply dual_residuation. apply wBIH_Deduction_Theorem. apply BiLEM.
  intros C HC ; inversion HC ; subst ; auto. inversion H.
- intro. destruct H as (l & H0 & H1 & H2).
  apply LEM_sSoundness in H2.
  assert (J0: (forall A, (Singleton _ # 0) A -> mforces M1 A)).
  { intros. inversion H. subst. intro. destruct w ; simpl ; auto.
    destruct u ; simpl ; auto. apply Fq. lia. }
  pose (H2 M1 J0 (UnDeux_I Un)). destruct l ; cbn in * ; try contradiction.
  destruct l ; cbn in *.
  + destruct w ; try contradiction. destruct (H1 f) ; auto.
    * inversion H3 ; subst. cbn in H. inversion H ; auto.
    * inversion H3; subst. cbn in H.
      pose (H (UnDeux_I Deux) Logic.I). apply f.
      intro. pose (H4 Trois). cbn in *. apply n ; auto.
      intros. destruct v ; auto. cbn. destruct u ; cbn in * ; auto.
      contradiction.
  + destruct l ; cbn in *.
    * destruct w.
      ++ destruct (H1 f) ; auto.
        -- inversion H3 ; subst. cbn in H. inversion H ; auto.
        -- inversion H3 ; subst. cbn in H.
          pose (H (UnDeux_I Deux) Logic.I). apply f.
          intro. pose (H4 Trois). cbn in *. apply n ; auto.
          intros. destruct v ; auto. cbn. destruct u ; cbn in * ; auto.
          contradiction.
      ++ destruct H ; try contradiction. destruct (H1 f0) ; auto.
        -- inversion H3 ; subst. cbn in H. inversion H ; auto.
        -- inversion H3 ; subst. cbn in H.
          pose (H (UnDeux_I Deux) Logic.I). apply f0.
          intro. pose (H4 Trois). cbn in *. apply n ; auto.
          intros. destruct v ; auto. cbn. destruct u ; cbn in * ; auto.
          contradiction.
    * inversion H0 ; subst. inversion H5 ; subst. inversion H7 ; subst.
      apply H4. destruct (H1 f) ; destruct (H1 f0) ; destruct (H1 f1) ; auto ;
      inversion H ; inversion H3 ; inversion H10 ; subst ; cbn ; auto.
      all: exfalso ; apply H6 ; cbn ; auto. 
Qed.

(* Validity on rooted models. *)

Lemma Rooted_models_validity : forall (M : model),
  (exists (r : @nodes M), forall w, (@reachable M r w)) ->
  (forall w, (wforces M w (Or (∞ # 0) (¬ ∞ # 0)))).
Proof.
intros. destruct H.
destruct (LEM (wforces M x (Var 0))).
- right. simpl. intros. apply H2. intros.
  apply (@persist M x) ; auto.
- left. simpl. intro. apply H0. apply H1 ; auto.
Qed.

(* Validity on rooted models, falsified on general models. *)

Lemma Consequences_Soundness4 :
  ~ sBIH_prv (Empty_set _) ((∞ # 0) ∨ (¬ ∞ # 0)).
Proof.
intro. apply LEM_sSoundness in H.
assert (J0: (forall A, In _ (Empty_set _) A ->
forall u : UnDeuxTrois, wforces M2 u A)).
{ intros. inversion H0. }
pose (H M2 J0 Trois).
destruct w.
- apply H0. intros. cbn in *. destruct v ; cbn in * ; auto.
  destruct u ; cbn in * ; auto.
- apply (H0 (UnDeux_I Deux) Logic.I).
  intro. pose (H1 (UnDeux_I Un)). cbn in * ; auto.
Qed.

End Counterexamples.

End ConseqSoundness.










