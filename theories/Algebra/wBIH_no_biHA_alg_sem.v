Require Import Ensembles.
Require Import Arith.
Require Import Lia.

Require Import Syntax.
Require Import Bi_Heyting_Algebras.
Require Import algebraic_semantic.
Require Import BIH_export.
Require Import Kripke_export.
Require Import wBIH_equivalential.
Require Import alg_soundness.
Require Import sBIH_alg_completeness.


Section model_construction.

Variable M : model.
Variable w : nodes.

Definition len_nodes (n : nat) := sigT (fun (x : prod nat nodes) => (fst x <= n)).

Definition Xmas_lightsM (n : nat) : model.
Proof.
unshelve eapply (@Build_model).
(* Nodes *)
- exact (len_nodes (S (2*n))).
(* Relation *)
- exact (fun x y => (((fst (projT1 x)) = (fst (projT1 y))) /\ reachable (snd (projT1 x)) (snd (projT1 y))) \/ (* Copy *)
  (Even (fst (projT1 x)) /\ (* Make a connection from an even number *)
   (((fst (projT1 x)) = S (fst (projT1 y))) \/ ((fst (projT1 y)) = S (fst (projT1 x)))) /\ (* Only connect to the next/previous odd number *)
   (reachable (snd (projT1 x)) (snd (projT1 y))) /\ (* Connect following the initial model *)
   (reachable (snd (projT1 x)) w) /\ (reachable w (snd (projT1 y))) (* Make sure we go through w *)
   )).
(* Valuation function *)
- exact (fun x p => val (snd (projT1 x)) p \/ (fst (projT1 x) = S (2*n))).
  (* Up to 2*n we copy the valuation of M, and then make everything true in
     S(2*n). *)
(* Reflexivity *)
- intros ; destruct u ; cbn ; destruct x ; subst ; cbn in *.
  left. split ; auto. apply reach_refl.
(* Transitivity *)
- intros u v r ; destruct u, v, r ; cbn ; destruct x,x0,x1 ; cbn in * ; subst.
  intros H0 H1. destruct H0,H1.
  + destruct H,H0 ; subst ; left ; firstorder. apply reach_tran with n3 ; auto.
  + destruct H ; subst. destruct H0 as (H0 & H2 & H3 & H4 & H5). right. repeat split ; auto.
    * apply reach_tran with n3 ; auto.
    * apply reach_tran with n3 ; auto.
  + destruct H0 ; subst. destruct H as (H0 & H2 & H3 & H4 & H5). right. repeat split ; auto.
    * apply reach_tran with n3 ; auto.
    * apply reach_tran with n3 ; auto.
  + destruct H as (H & H2 & H3 & H4 & H5). destruct H0 as (H6 & H7 & H8 & H9 & H10).
    destruct H2,H7 ; subst ; auto.
    * exfalso ; destruct H,H6 ; lia.
    * left ; split ; auto. apply reach_tran with n3 ; auto.
    * inversion H1 ; subst. exfalso ; destruct H,H6 ; lia.
    * exfalso ; destruct H,H6 ; lia.
(* Persistence *)
- cbn. intros. destruct u,v ; cbn in *. destruct x,x0 ; cbn in * ; subst.
  destruct H.
  + destruct H ; subst. destruct H0 ; subst ; auto.
    left ; apply persist with n1 ; auto.
  + destruct H as (H & H2 & H3 & H4 & H5). destruct H0 ; subst ; auto.
    * left ; apply persist with n1 ; auto.
    * exfalso. destruct H ; lia.
Defined.

Definition zw n : (@nodes (Xmas_lightsM n)).
Proof.
exists (0, w) ; cbn. apply le_0_n.
Defined.

Definition vm (v : @nodes M) (m n : nat) (mleqn : m <= (S (2*n))): (@nodes (Xmas_lightsM n)).
Proof.
exists (m, v) ; cbn.
destruct m.
- apply le_0_n.
- lia.
Defined.

Definition lnc (v : @nodes M) m n (mleqn : m <= n): len_nodes n.
Proof.
exists (m,v). auto.
Defined.


Lemma Xmas_lightsM_nbisim_M : forall j n k v kv,
    k <= (2*n) -> (projT1 kv) = (k,v) -> 
    j <= (2*n) - k -> n_bisimulation j M (Xmas_lightsM n) v kv.
Proof.
apply (well_founded_induction_type lt_wf (fun j => forall n k v kv,
    k <= (2*n) -> (projT1 kv) = (k,v) -> 
    j <= (2*n) - k -> n_bisimulation j M (Xmas_lightsM n) v kv)).
intros j IHj. destruct j.
- intros n k v kv Hk Hkv H. cbn. destruct kv ; destruct x ; cbn in * ; inversion Hkv ; subst.
  intro p. split ; intro ; auto. destruct H0 ; auto. lia. 
- intros n k v kv Hk Hkv H. destruct kv eqn:Ekv ; destruct x eqn:Ex ; cbn in * ; inversion Hkv ; subst.
  repeat split.
  + intro ; left ; subst ; cbn in * ; inversion H ; subst ; auto.
  + intro H0 ; destruct H0 ; auto. lia.
  + intros v1 H0. destruct H0.
    * destruct H0 ; subst. exists (snd (projT1 v1)). split ; auto.
      destruct (projT1 v1) eqn:Ep1v1 ; cbn in * ; subst.
      apply IHj with n0 ; try lia ; auto.
    * destruct H0 as (H2 & H3 & H4 & H5 & H6). exists (snd (projT1 v1)) ; split ; auto.
      destruct H3.
      -- apply IHj with (fst (projT1 v1)) ; try lia. destruct v1 ; destruct x ; cbn ; subst ; auto.
      -- apply IHj with (fst (projT1 v1)) ; try lia. destruct v1 ; destruct x ; cbn ; subst ; auto.
  + intros v1 H0. exists (lnc v1 k (S (n + (n + 0))) l). split ; auto.
    apply IHj with k ; try lia. cbn ; auto.
  + intros v1 H0. destruct H0.
    * destruct H0 ; subst. exists (snd (projT1 v1)). split ; auto.
      destruct (projT1 v1) eqn:Ep1v1 ; cbn in * ; subst.
      apply IHj with n0 ; try lia ; auto.
    * destruct H0 as (H2 & H3 & H4 & H5 & H6). exists (snd (projT1 v1)) ; split ; auto.
      destruct H3.
      -- apply IHj with (fst (projT1 v1)) ; try lia. destruct v1 ; destruct x ; cbn ; subst ; auto.
      -- apply IHj with (fst (projT1 v1)) ; try lia. destruct v1 ; destruct x ; cbn ; subst ; auto.
  + intros v1 H0. exists (lnc v1 k (S (n + (n + 0))) l). split ; auto.
    apply IHj with k ; try lia. cbn ; auto.
Qed.

Lemma w_Xmas_lightsM_nbisim_M n : n_bisimulation (2*n) M (Xmas_lightsM n) w (zw n).
Proof.
apply Xmas_lightsM_nbisim_M with (k:=0) ; cbn ; auto ; lia.
Qed.

Lemma n_reachable_Xmas m n (H: n <= (S (2 * m))) : n_reachable (Xmas_lightsM m) n (zw m) (vm w n m H).
Proof.
induction n.
- cbn. destruct m ; unfold vm ; cbn ; auto.
- cbn. assert (n <= S (2 * m)). lia. exists (vm w n m H0) ; cbn.
  split.
  + destruct (Even_Odd_dec n).
    * left. right. repeat split ; try apply reach_refl ; auto.
    * right. right. repeat split ; try apply reach_refl ; auto. destruct H1 ; subst ; cbn.
      exists (S x). lia.
  + auto.
Qed.

Lemma n_reachable_head : forall n M w v, n_reachable M (S n) w v ->
  exists u, (reachable w u \/ reachable u w) /\ n_reachable M n u v.
Proof.
induction n ; cbn ; intros.
- destruct H as (x & Hx0 & Hx1) ; subst. firstorder.
- destruct H as (x & Hx0 & Hx1). apply IHn in Hx1. firstorder.
Qed.

Lemma n_reachable_sym : forall n M w v, n_reachable M n w v -> n_reachable M n v w.
Proof.
induction n.
- intros ; cbn ; auto.
- intros ; cbn in *. 
  apply n_reachable_head in H. destruct H as (x & Hx0 & Hx1).
  exists x. firstorder.
Qed.

End model_construction.




Section No_biHA_semantics.

  Variable Hypirrel : forall Γ Φ Ψ, (@setform Γ Φ = @setform Γ Ψ) -> Φ = Ψ. 

  Lemma alg_eq_iff_wBIH_eqprv : forall ϕ ψ,
    alg_eqconseq_eq (fun _ _ : form => False) ϕ ψ <->
    (wBIH_prv (Singleton form ϕ) ψ /\ wBIH_prv (Singleton form ψ) ϕ).
  Proof.
  intros ϕ ψ ; split ; intro H ; [split | destruct H as (H0 & H1)].
  - apply wBIH_monot with (Γ:= Union _ (Empty_set _) (Singleton form ϕ)) ; 
    [apply wBIH_Detachment_Theorem | intros A HA ; inversion HA ; auto ; inversion H0 ; subst].
    apply sBIH_wBIH_same_thms. apply alg_completeness_sBIH ;
    [ intros ; auto | intros χ δ H0 A amap H1]. destruct H0 ; subst ; cbn.
    apply aleq_antisym ; [apply high_one | apply ord_resid].
    pose (H A amap) ; rewrite e ; [ apply meet_elim2 | intros ; contradiction].
  - apply wBIH_monot with (Γ:= Union _ (Empty_set _) (Singleton form ψ)) ; 
    [apply wBIH_Detachment_Theorem | intros A HA ; inversion HA ; auto ; inversion H0 ; subst].
    apply sBIH_wBIH_same_thms. apply alg_completeness_sBIH ;
    [ intros ; auto | intros χ δ H0 A amap H1]. destruct H0 ; subst ; cbn.
    apply aleq_antisym ; [apply high_one | apply ord_resid].
    pose (H A amap) ; rewrite e ; [ apply meet_elim2 | intros ; contradiction].
  - apply wBIH_monot with (Γ1:= Union _ (Empty_set _) (Singleton form ϕ)) in H0 ;
    [apply wBIH_Deduction_Theorem in H0 | intros A HA ; right ; auto].
    apply wBIH_monot with (Γ1:=Union _ (Empty_set _) (Singleton form ψ)) in H1 ; 
    [apply wBIH_Deduction_Theorem in H1 | intros A HA ; right ; auto].
    apply algord_soundness_wBIH in H0,H1.
    intros A amap H3.
    apply aleq_antisym.
      + apply aleq_trans with (meet one (interp A amap ϕ)).
        * apply glb.
          -- apply high_one.
          -- apply aleq_refl.
        * apply ord_resid. apply H0. intros γ H4 ; inversion H4.
      + apply aleq_trans with (meet one (interp A amap ψ)).
        * apply glb.
          -- apply high_one.
          -- apply aleq_refl.
        * apply ord_resid. apply H1. intros γ H4 ; inversion H4.
  Qed.

Axiom LEM : forall P, P \/ ~ P.

Variable Eq : form -> form -> Prop.

Hypothesis wBIH_alg_sem : forall Γ ϕ, alg_eqconseq Eq Γ ϕ -> wBIH_prv Γ ϕ.

Lemma Eq_elem_invalid : exists ϕ ψ, Eq ϕ ψ /\ ~ alg_eqconseq_eq (fun x y => False) ϕ ψ.
Proof.
epose (LEM _) ; destruct o as [ P | NP ] ; [exact P | exfalso].
assert (forall ϕ ψ : form, Eq ϕ ψ -> alg_eqconseq_eq (fun _ _ : form => False) ϕ ψ).
{ intros. destruct (LEM (alg_eqconseq_eq (fun _ _ : form => False) ϕ ψ)) as [H' | H'] ; [auto | exfalso].
  apply NP. exists ϕ,ψ ; firstorder. }
assert (forall Γ χ, wBIH_prv Γ χ).
{ intros Γ χ. apply wBIH_alg_sem. intros ϕ ψ E A amap H0.
  repeat rewrite first_subst_interp. apply H ; auto.
  intros ; contradiction. }
apply Consequences_Soundness1. apply H0.
Qed.

Lemma No_wBIH_alg_sem : False.
Proof.
destruct Eq_elem_invalid as (ϕ & ψ & H & H0).
(* We prove that one of ϕ ⊢ ψ and ψ ⊢ ϕ does not hold,
   using the lemma alg_eq_iff_wBIH_eqprv above. *)
assert ((~ wBIH_prv (Singleton _ ϕ) ψ) \/ (~ wBIH_prv (Singleton _ ψ) ϕ)).
{ rewrite alg_eq_iff_wBIH_eqprv in H0.
  epose (LEM _) ; destruct o as [ P | NP ] ; [exact P | exfalso].
  apply NP. left ; intro. apply NP ; right ; intro.
  apply H0 ; split ; auto. }
(* We make a case distinction on whether it is ϕ ⊢ ψ or ψ ⊢ ϕ
   which does not hold. *)
destruct H1 as [H1 | H1].
(* Case where ϕ ⊢ ψ does not hold. *)
- (* Then there must be by completeness a model M and a world w
     forcing ϕ but not ψ. *) 
  assert (exists M w, wforces M w ϕ /\ ~ wforces M w ψ).
  { epose (LEM _) ; destruct o as [ P | NP ] ; [exact P | exfalso].
    apply H1. apply wCompleteness. intros M w Hw.
    epose (LEM _) ; destruct o as [ P' | NP' ] ; [exact P' | exfalso].
    apply NP. exists M,w ; firstorder. }
  destruct H2 as (M & w & Hw1 & Hw2).
  remember (max (depth ϕ) (depth (ψ))) as n.
  (* We can generate the Christmas-lights model generated from M and w,
     taking the maximal depth n of ϕ and ψ to determine how many zigzags
     we need in the constructed models. *)
  pose (Xmas_lightsM M w n) as XMAS.
  pose (vm M w w (S (2*n)) n (le_n (S (2*n)))) as WN.
  pose (zw M w n) as WO.
  (* Of course, the Christmas-lights model forces ϕ in its
     initial point WO.*)
  assert (WO1: wforces XMAS WO ϕ).
  { pose (w_Xmas_lightsM_nbisim_M M w n).
    apply n_bisimulation_imp_n_depth_equiv with (ϕ:=ϕ) in n0 ; try lia.
    apply n0 ; auto. }
  (* It also does not forces ψ, again using n-bisimulation. *)
  assert (WO2: ~ wforces XMAS WO ψ).
  { intro. apply Hw2.
    pose (w_Xmas_lightsM_nbisim_M M w n).
    apply n_bisimulation_imp_n_depth_equiv with (ϕ:=ψ) in n0 ; try lia.
    apply n0 ; auto. }
  (* But, by construction the Christmas-lights model forces the propositional
     variable #0 in the world WN the extra (2*n)+1 copy of M. *)
  assert (WN1: wforces XMAS WN #0).
  { cbn ; auto. }
  (* WN forces the formula below, as it is a validity. *)
  assert (WN2: wforces XMAS WN (DN_form (S n) (ψ --> ψ))).
  { apply DN_form_n_reachable. intros. intros u vRu Hu. auto. }
  (* But does not force the formula below, as it can see WO in n+1 zigzags. *)
  assert (WN3: ~ wforces XMAS WN (DN_form (S n) (ϕ --> ψ))).
  { intro. apply Hw2. pose (w_Xmas_lightsM_nbisim_M M w n).
    apply n_bisimulation_imp_n_depth_equiv with (ϕ:=ψ) in n0 ; try lia.
    apply n0. pose (n_reachable_DN_clos _ _ _ _ H2 (S (2 * n)) WO).
    apply w0 ; try lia ; auto.
    - apply n_reachable_sym. apply n_reachable_Xmas. 
    - apply reach_refl. }
  (* The last three statements above are in contradiction with Theorem 2.16
     of the 2003 paper of Blok and Rebagliato. We use this insight to prove
     the contradiction without formalising their general Theorem. *)
  enough (~ wBIH_prv (fun x => x = (# 0) \/ x = (DN_form (S n) (ψ --> ψ))) (DN_form (S n) (ϕ --> ψ))).
  (* We first prove that the fact that #0, (¬∼)^{n+1} (ψ → ψ) ⊢ (¬∼)^{n+1} (ϕ → ψ) not holding
     leads to a contradiction, inspiring ourselves from Blok and Rebagliato. *)
  + apply H2. apply wBIH_alg_sem. intros B C EBC A amap H3.
    repeat rewrite first_subst_interp.
    rewrite DN_form_interp. simpl (interp A amap (ϕ --> ψ)).
    assert (interp A amap ϕ = interp A amap ψ).
    { rewrite (first_subst_idem ϕ),(first_subst_idem ψ). apply H3.
      exists ϕ,ψ. split ; auto. exists #0 ; split ; auto. }
    rewrite H4.
    enough (interp A amap (first_subst (DN_form (S n) (ψ --> ψ)) B) =
    interp A amap (first_subst (DN_form (S n) (ψ --> ψ)) C)).
    * repeat rewrite first_subst_interp, DN_form_interp in H5 ; auto.
    * apply H3. exists B,C ; split ; auto. exists (DN_form (S n) (ψ --> ψ)) ; auto.
  (* Second, we prove that the fact that #0, (¬∼)^{n+1} (ψ → ψ) ⊢ (¬∼)^{n+1} (ϕ → ψ) does not hold
     indeed follows from our set of assumptions. *)
  + intro. apply WN3. apply LEM_wSoundness in H2. apply H2. intros B HB ; destruct HB ; subst ; auto.
(* Case where ψ ⊢ ϕ does not hold. This case is symmetric to the previous one. *)
- assert (exists M w, wforces M w ψ /\ ~ wforces M w ϕ).
  { epose (LEM _) ; destruct o as [ P | NP ] ; [exact P | exfalso].
    apply H1. apply wCompleteness. intros M w Hw.
    epose (LEM _) ; destruct o as [ P' | NP' ] ; [exact P' | exfalso].
    apply NP. exists M,w ; firstorder. }
  destruct H2 as (M & w & Hw1 & Hw2).
  remember (max (depth ϕ) (depth (ψ))) as n.
  pose (Xmas_lightsM M w n) as XMAS.
  pose (vm M w w (S (2*n)) n (le_n (S (2*n)))) as WN.
  pose (zw M w n) as WO.
  assert (WO1: wforces XMAS WO ψ).
  { pose (w_Xmas_lightsM_nbisim_M M w n).
    apply n_bisimulation_imp_n_depth_equiv with (ϕ:=ψ) in n0 ; try lia.
    apply n0 ; auto. }
  assert (WO2: ~ wforces XMAS WO ϕ).
  { intro. apply Hw2.
    pose (w_Xmas_lightsM_nbisim_M M w n).
    apply n_bisimulation_imp_n_depth_equiv with (ϕ:=ϕ) in n0 ; try lia.
    apply n0 ; auto. }
  assert (WN1: wforces XMAS WN #0).
  { cbn ; auto. }
  assert (WN2: wforces XMAS WN (DN_form (S n) (ϕ --> ϕ))).
  { apply DN_form_n_reachable. intros. intros u vRu Hu. auto. }
  assert (WN3: ~ wforces XMAS WN (DN_form (S n) (ψ --> ϕ))).
  { intro. apply Hw2. pose (w_Xmas_lightsM_nbisim_M M w n).
    apply n_bisimulation_imp_n_depth_equiv with (ϕ:=ϕ) in n0 ; try lia.
    apply n0. pose (n_reachable_DN_clos _ _ _ _ H2 (S (2 * n)) WO).
    apply w0 ; try lia ; auto.
    - apply n_reachable_sym. apply n_reachable_Xmas. 
    - apply reach_refl. }
  enough (~ wBIH_prv (fun x => x = (# 0) \/ x = (DN_form (S n) (ϕ --> ϕ))) (DN_form (S n) (ψ --> ϕ))).
  + apply H2. apply wBIH_alg_sem. intros B C EBC A amap H3.
    repeat rewrite first_subst_interp.
    rewrite DN_form_interp. simpl (interp A amap (ψ --> ϕ)).
    assert (interp A amap ϕ = interp A amap ψ).
    { rewrite (first_subst_idem ϕ),(first_subst_idem ψ). apply H3.
      exists ϕ,ψ. split ; auto. exists #0 ; split ; auto. }
    rewrite <- H4.
    enough (interp A amap (first_subst (DN_form (S n) (ϕ --> ϕ)) B) =
    interp A amap (first_subst (DN_form (S n) (ϕ --> ϕ)) C)).
    * repeat rewrite first_subst_interp, DN_form_interp in H5 ; auto.
    * apply H3. exists B,C ; split ; auto. exists (DN_form (S n) (ϕ --> ϕ)) ; auto.
  + intro. apply WN3. apply LEM_wSoundness in H2. apply H2. intros B HB ; destruct HB ; subst ; auto.
Qed.

End No_biHA_semantics.
