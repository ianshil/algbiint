Require Import Ensembles.

Require Import Syntax.
Require Import Bi_Heyting_Algebras.
Require Import algebraic_semantic.
Require Import alg_soundness.
Require Import BIH_export.

Section filters.

Class wBIH_filter (A : biHalg) :=
    {
        d_filter : nodes -> Prop ;
        wBIH_closed : forall Γ ϕ, wBIH_prv Γ ϕ -> 
                            forall amap, (forall γ, Γ γ -> d_filter (interp A amap γ)) ->
                                          d_filter (interp A amap ϕ)
    }.

Class lattice_filter (A : biHalg) :=
    {
        l_filter : nodes -> Prop ;
        contains_one : l_filter one ;
        aleq_closed : forall a b, aleq A a b -> l_filter a -> l_filter b ;
        meet_closed : forall a b, l_filter a -> l_filter b -> l_filter (meet a b) ;
    }.

Lemma d_to_l_filter A (df : wBIH_filter A) : lattice_filter A.
Proof.
unshelve eapply (@Build_lattice_filter).
- exact d_filter.
- pose (wBIH_closed _ _ (prv_Top (Empty_set _)) (fun _ => one)).
  cbn in d. apply d. intros. inversion H.
- intros a b H H0.
  assert (H1: rpc a b = one).
  { apply aleq_antisym.
    - apply high_one.
    - apply ord_resid. rewrite mcomm. rewrite greatest. auto. }
  assert (H2: wBIH_prv (fun x : form => x = # 0 \/ x = # 0 --> # 1) # 1).
  { eapply wMP.
    - apply wId ; right ; split.
    - apply wId ; left ; split. }
  pose (wBIH_closed _ _ H2 (fun n => match n with | 0 => a | 1 => b | _ => one end)).
  cbn in d ; apply d. intros. destruct H3 ; subst ; cbn ; auto.
  rewrite H1.
  pose (wBIH_closed _ _ (prv_Top (Empty_set _)) (fun _ => one)).
  cbn in d0. apply d0. intros. inversion H3.
- intros a b H H0.
  assert (H1: wBIH_prv (fun x : form => x = # 0 \/ x = # 1) (#0 ∧ # 1)).
  { eapply wMP.
    - eapply wMP.
      + eapply wMP.
        * apply wAx ; eapply A8 ; reflexivity.
        * eapply imp_Id_gen.
      + apply wBIH_Deduction_Theorem ; apply wId ; left ; right ; split.
    - apply wId ; left ; split. }
  pose (wBIH_closed _ _ H1 (fun n => match n with | 0 => a | 1 => b | _ => one end)).
  cbn in d ; apply d. intros. destruct H2 ; subst ; cbn ; auto.
Qed.

Lemma l_to_d_filter A (lf : lattice_filter A) : wBIH_filter A.
Proof.
unshelve eapply (@Build_wBIH_filter).
- exact l_filter.
- intros Γ ϕ D. induction D ; intros.
  + apply H0 ; auto.
  + enough (one = (interp A amap A0)).
    * rewrite <- H1. apply contains_one.
    * apply aleq_antisym.
      -- apply Axioms_one ; auto.
      -- apply high_one.
  + pose (IHD1 _ H). pose (IHD2 _ H). cbn in l.
    eapply aleq_closed.
    * apply mp.
    * apply meet_closed.
      -- exact l0.
      -- auto.
  + cbn. enough (H1: one = (rpc (subtr one (interp A amap A0)) zero)).
    * rewrite <- H1. apply contains_one.
    * apply aleq_antisym.
      -- apply ord_resid. rewrite mcomm. rewrite greatest.
         apply ord_dresid. rewrite lowest.
         apply sBIH_extens_wBIH in D.
         apply alg_soundness_sBIH in D.
         assert (H2: sEq (#0) ⊤).
         { split ; auto. }
         pose (D _ _ H2 A amap). cbn in e. rewrite e.
         ++ apply aleq_refl.
         ++ intros. destruct H0 as (C & E & H3 & (G & H4 & H5)) ; inversion H4. 
      -- apply high_one.
Qed.

End filters.



Section congruences.

Class congruence (A : biHalg) :=
  {
     cong : nodes -> nodes -> Prop ;
     cong_refl a : cong a a ;
     cong_sym a b : cong a b -> cong b a ;
     cong_trans a b c : cong a b -> cong b c -> cong a c ; 
     cong_meet a0 a1 b0 b1 : cong a0 a1 -> cong b0 b1 -> cong (meet a0 b0) (meet a1 b1) ;
     cong_join a0 a1 b0 b1 : cong a0 a1 -> cong b0 b1 -> cong (join a0 b0) (join a1 b1) ;
     cong_rpc a0 a1 b0 b1 : cong a0 a1 -> cong b0 b1 -> cong (rpc a0 b0) (rpc a1 b1) ;
     cong_subtr a0 a1 b0 b1 : cong a0 a1 -> cong b0 b1 -> cong (subtr a0 b0) (subtr a1 b1) ;
  }.

End congruences.




Section no_isomorphism.

Inductive zho_type :=
  | Zero : zho_type
  | Half : zho_type
  | One : zho_type.

Inductive zho_leq : zho_type -> zho_type -> Prop :=
  | Zero_low a : zho_leq Zero a 
  | One_high a : zho_leq a One
  | zho_leq_refl a : zho_leq a a.

Lemma dec_zho_leq a b : {zho_leq a b} + {~ zho_leq a b}.
Proof.
destruct a eqn:Ha.
- left. apply Zero_low.
- destruct b eqn:Hb.
  + right. intro. inversion H.
  + left. apply zho_leq_refl.
  + left. apply One_high.
- subst. destruct b ; auto.
  + right. intro. inversion H.
  + right. intro. inversion H.
  + left. apply One_high.
Qed.

Lemma dec_zho_leq_qel a b : {zho_leq a b} + {zho_leq b a}.
Proof.
destruct a eqn:Ha.
- left. apply Zero_low.
- destruct b eqn:Hb.
  + right. apply Zero_low.
  + left. apply zho_leq_refl.
  + left. apply One_high.
- subst. right ; apply One_high.
Qed.

Definition lower : zho_type -> zho_type -> zho_type.
Proof.
intros a b. 
destruct (dec_zho_leq a b).
- exact a.
- exact b.
Defined.

Definition higher : zho_type -> zho_type -> zho_type.
Proof.
intros a b. 
destruct (dec_zho_leq a b).
- exact b.
- exact a.
Defined.

(* We define the bi-Heyting algebra on the three elements chain. *)

Definition zho_alg : biHalg.
Proof.
unshelve eapply (@Build_biHalg).
- exact zho_type. 
- exact One.
- exact Zero.
- exact lower.
- exact higher.
- intros a b. destruct (dec_zho_leq a b).
  + exact One.
  + exact b.
- intros a b. destruct (dec_zho_leq a b).
  + exact Zero.
  + exact a.
- intros ; cbn in * ; unfold lower ; destruct (dec_zho_leq a One) ; auto. 
  exfalso ; apply n ; apply One_high.
- intros ; cbn in * ; unfold higher ; destruct (dec_zho_leq a Zero) ; auto ; 
  inversion z ; auto.
- intros ; unfold lower ; destruct (dec_zho_leq a b) ; destruct (dec_zho_leq b a) ; auto.
  inversion z ; inversion z0 ; subst ; auto ; discriminate.
  destruct (dec_zho_leq_qel a b) ; exfalso ; auto.
- intros ; unfold lower ; destruct (dec_zho_leq b c) ; destruct (dec_zho_leq a b) ; auto.
  + destruct (dec_zho_leq a c) ; auto. exfalso ; apply n. inversion z ; inversion z0 ; subst ; auto ; try discriminate.
    apply One_high.
  + destruct (dec_zho_leq b c) ; auto. exfalso ; auto.
  + destruct (dec_zho_leq a c) ; auto ; destruct (dec_zho_leq b c) ; auto.
    exfalso ; auto. exfalso ; apply n1. destruct (dec_zho_leq_qel a b) ; auto.
    exfalso ; auto. inversion z ; inversion z0 ; subst ; auto ; try discriminate.
    apply One_high. exfalso ; auto.
- intros ; unfold lower ; unfold higher.
  destruct (dec_zho_leq a b) ; auto.
  + destruct (dec_zho_leq a b) ; auto. exfalso ; auto.
  + destruct (dec_zho_leq a a) ; auto.
- intros ; unfold higher ; destruct (dec_zho_leq a b) ; destruct (dec_zho_leq b a) ; auto.
  inversion z ; inversion z0 ; subst ; auto ; discriminate.
  destruct (dec_zho_leq_qel a b) ; exfalso ; auto.
- intros ; unfold higher ; destruct (dec_zho_leq b c) ; destruct (dec_zho_leq a b) ; auto.
  + destruct (dec_zho_leq a c) ; auto ; destruct (dec_zho_leq b c) ; auto.
    exfalso ; auto. exfalso ; apply n. inversion z ; inversion z0 ; subst ; auto ; try discriminate.
    apply One_high. exfalso ; auto.
  + destruct (dec_zho_leq b c) ; auto. exfalso ; auto.
  + destruct (dec_zho_leq a c) ; auto. destruct (dec_zho_leq_qel b c).
    exfalso ; auto. exfalso ; apply n0. inversion z ; inversion z0 ; subst ; auto ; try discriminate.
    apply One_high.
- intros ; unfold lower ; unfold higher.
  destruct (dec_zho_leq a b) ; auto.
  + destruct (dec_zho_leq a a) ; auto.
  + destruct (dec_zho_leq a b) ; auto. exfalso ; auto.
(* Implication case *)
- intros. unfold lower ; cbn. split ; intro.
  + destruct (dec_zho_leq a b) ; cbn in *.
    * destruct (dec_zho_leq a c) ; cbn in * ; auto.
      destruct (dec_zho_leq b c) ; cbn in * ; auto.
      -- destruct (dec_zho_leq a One) ; cbn in * ; subst ; auto.
         exfalso ; apply n.
         inversion z1 ; inversion z ; inversion z0 ; subst ; auto ; discriminate.
         exfalso ; apply n0 ; apply zho_leq_refl.
      -- destruct (dec_zho_leq a c) ; cbn in * ; subst ; auto. exfalso ; auto.
    * destruct (dec_zho_leq b c) ; cbn in * ; auto.
      destruct (dec_zho_leq a c) ; cbn in * ; auto.
      -- destruct (dec_zho_leq_qel b c). exfalso ; auto.
         destruct (dec_zho_leq_qel a b). exfalso ; auto.
         inversion z1 ; inversion z ; inversion z0 ; subst ; auto ; discriminate.
      -- subst. exfalso ; apply n1 ; apply zho_leq_refl.
  + destruct (dec_zho_leq a b) ; cbn in * ; subst ; auto.
    -- destruct (dec_zho_leq b c) ; cbn in * ; auto.
       destruct (dec_zho_leq a One) ; cbn in * ; auto.
       exfalso ; apply n ; apply One_high.
    -- destruct (dec_zho_leq b c) ; cbn in * ; auto.
       ++ destruct (dec_zho_leq a One) ; cbn in * ; auto.
          exfalso ; apply n0 ; apply One_high.
       ++ subst. exfalso ; apply n0 ; apply zho_leq_refl.
(* Exclusion case *)
- intros. unfold higher,lower ; cbn. split ; intro.
  + destruct (dec_zho_leq a b) ; cbn in *.
    * destruct (dec_zho_leq b c) ; cbn in * ; auto.
      -- destruct (dec_zho_leq a c) ; cbn in * ; subst ; auto.
         exfalso ; apply n.
         inversion z ; inversion z0 ; subst ; auto ; try discriminate. apply One_high.
      -- destruct (dec_zho_leq a b) ; cbn in * ; subst ; auto. exfalso ; auto.
    * destruct (dec_zho_leq b c) ; cbn in * ; auto.
      destruct (dec_zho_leq a c) ; cbn in * ; auto.
      -- destruct (dec_zho_leq a b) ; auto.
         destruct (dec_zho_leq_qel b c). exfalso ; auto.
         destruct (dec_zho_leq_qel a b). exfalso ; auto.
         inversion z1 ; inversion z ; inversion z0 ; subst ; auto ; discriminate.
      -- subst. exfalso ; apply n1 ; apply zho_leq_refl.
  + destruct (dec_zho_leq a b) ; cbn in * ; subst ; auto.
    -- destruct (dec_zho_leq b c) ; cbn in * ; auto.
       destruct (dec_zho_leq Zero c) ; cbn in * ; auto.
       exfalso ; apply n ; apply Zero_low.
       destruct (dec_zho_leq Zero c) ; cbn in * ; auto.
       exfalso ; apply n0 ; apply Zero_low.
    -- destruct (dec_zho_leq b c) ; cbn in * ; auto.
       ++ destruct (dec_zho_leq a c) ; cbn in * ; auto.
          destruct (dec_zho_leq a b) ; cbn in * ; auto.
          ** exfalso ; auto.
          ** subst. exfalso ; apply n2 ; apply zho_leq_refl.
Defined.

Definition first_zho_lattice_filters : lattice_filter zho_alg.
Proof.
unshelve eapply (@Build_lattice_filter).
- exact (fun _ => True).
- cbn ; auto.
- intros ; cbn ; auto.
- intros ; cbn ; auto.
Defined.

Definition second_zho_lattice_filters : lattice_filter zho_alg.
Proof.
unshelve eapply (@Build_lattice_filter).
- exact (fun x => zho_leq Half x).
- cbn ; apply One_high.
- intros ; cbn in *. destruct a,b ; subst ; auto.
  1-2: inversion H0. 
  + unfold aleq in H ; unfold meet in H ; cbn in * ; unfold lower in H.
    destruct (dec_zho_leq Half Zero) ; auto ; discriminate.
  + apply One_high.
  + unfold aleq in H ; unfold meet in H ; cbn in * ; unfold lower in H.
    destruct (dec_zho_leq One Zero) ; auto ; try inversion z ; try discriminate.
  + apply zho_leq_refl.
- intros ; cbn in *. unfold lower. destruct (dec_zho_leq a b) ; subst ; auto.
Defined.

Definition three_zho_lattice_filters : lattice_filter zho_alg.
Proof.
unshelve eapply (@Build_lattice_filter).
- exact (fun x => x = One).
- cbn ; auto.
- intros ; cbn in * ; subst. inversion H. unfold lower in H1.
  destruct (dec_zho_leq One b) ; auto. inversion z ; auto.
- intros ; cbn in * ; subst ; auto. unfold lower.
  destruct (dec_zho_leq One One) ; subst ; auto.
Defined.

Axiom LEM : forall P, P \/ ~ P.

Lemma only_two_zho_congruences : forall (c : congruence zho_alg),
  (forall a b, cong a b <-> (fun x y => x = y) a b) \/
  (forall a b, cong a b <-> (fun x y => True) a b).
Proof.
intro c.
destruct (LEM (forall a b : nodes, cong a b <-> a = b)) ; auto.
right. intros a b ; split ; intro H0 ; auto.
assert (exists a b, a <> b /\ cong a b).
{ destruct (LEM (exists a b, a <> b /\ cong a b)) ; auto.
  exfalso. apply H. intros. split ; intro H2.
  - destruct a0,b0 ; auto ; exfalso ; apply H1 ; eexists _,_ ; split ; try exact H2 ; intro H3 ; discriminate.
  - subst ; apply cong_refl. }
destruct H1 as (d & e & H1 & H2).
destruct d,e ; try contradiction.
3,5,6: apply cong_sym in H2.
- assert (H3: cong (@rpc zho_alg Zero Zero) (@rpc zho_alg Half Zero)).
  { apply cong_rpc ; auto. apply cong_refl. }
  cbn in H3. destruct (dec_zho_leq Zero Zero) ; [  | exfalso ; apply n ; apply zho_leq_refl ].
  destruct (dec_zho_leq Half Zero) ; [ inversion z0| ].
  assert (H4: @cong _ c One Half).
  { apply cong_trans with Zero ; auto. }
  destruct a,b ; auto ; try apply cong_sym ; auto ; try apply cong_refl.
- assert (H3: cong (@meet zho_alg Zero Half) (@meet zho_alg One Half)).
  { apply cong_meet ; auto. apply cong_refl. }
  cbn in H3 ; unfold lower in H3. destruct (dec_zho_leq Zero Half) ; [  | exfalso ; apply n ; apply Zero_low ].
  destruct (dec_zho_leq One Half) ; [ inversion z0 | ].
  assert (H4: @cong _ c One Half).
  { apply cong_trans with Zero ; auto. apply cong_sym ; auto. }
  destruct a,b ; auto ; try apply cong_sym ; auto ; try apply cong_refl.
- assert (H3: cong (@rpc zho_alg Zero Zero) (@rpc zho_alg Half Zero)).
  { apply cong_rpc ; auto. apply cong_refl. }
  cbn in H3. destruct (dec_zho_leq Zero Zero) ; [  | exfalso ; apply n ; apply zho_leq_refl ].
  destruct (dec_zho_leq Half Zero) ; [ inversion z0| ].
  assert (H4: @cong _ c One Half).
  { apply cong_trans with Zero ; auto. }
  destruct a,b ; auto ; try apply cong_sym ; auto ; try apply cong_refl.
- assert (H3: cong (@meet zho_alg Zero Half) (@meet zho_alg One Half)).
  { apply cong_meet ; auto. apply cong_refl. }
  cbn in H3 ; unfold lower in H3. destruct (dec_zho_leq Zero Half) ; [  | exfalso ; apply n ; apply Zero_low ].
  destruct (dec_zho_leq One Half) ; [ inversion z0 | ].
  assert (H4: @cong _ c One Half).
  { apply cong_trans with Zero ; auto. apply cong_sym ; auto. }
  destruct a,b ; auto ; try apply cong_sym ; auto ; try apply cong_refl.
- assert (H3: cong (@subtr zho_alg One Half) (@subtr zho_alg One One)).
  { apply cong_subtr ; auto. apply cong_refl. }
  cbn in H3 ; unfold lower in H3.
  destruct (dec_zho_leq One Half) ; [ inversion z | ].
  destruct (dec_zho_leq One One) ; [ | exfalso ; apply n0 ; apply zho_leq_refl ].
  assert (H4: @cong _ c Zero Half).
  { apply cong_trans with One ; apply cong_sym ; auto. }
  destruct a,b ; auto ; try apply cong_sym ; auto ; try apply cong_refl.
- assert (H3: cong (@subtr zho_alg One Half) (@subtr zho_alg One One)).
  { apply cong_subtr ; auto. apply cong_refl. }
  cbn in H3 ; unfold lower in H3.
  destruct (dec_zho_leq One Half) ; [ inversion z | ].
  destruct (dec_zho_leq One One) ; [ | exfalso ; apply n0 ; apply zho_leq_refl ].
  assert (H4: @cong _ c Zero Half).
  { apply cong_trans with One ; apply cong_sym ; auto. }
  destruct a,b ; auto ; try apply cong_sym ; auto ; try apply cong_refl.
Qed.

End no_isomorphism.