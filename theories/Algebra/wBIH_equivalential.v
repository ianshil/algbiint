Require Import Ensembles.
Require Import Arith.
Require Import Lia.

Require Import Syntax.
Require Import BIH_export.
Require Import Kripke_export.

Section equivalential.

Definition clos_DN_eq ϕ ψ χ : Prop := exists n, χ = DN_form n (ϕ <--> ψ).

Theorem wBIH_R ϕ : forall χ, clos_DN_eq ϕ ϕ χ -> wBIH_prv (Empty_set _) χ.
Proof.
intros χ (n & Hn) ; subst.
induction n ; cbn.
- eapply wMP ; [ | apply prv_Top]. eapply wMP.
  + eapply wMP.
    * apply wAx ; eapply A8 ; reflexivity.
    * eapply wMP ; [ apply Thm_irrel | apply imp_Id_gen].
  + eapply wMP ; [ apply Thm_irrel | apply imp_Id_gen].
- apply wDN ; auto.
Qed.

Theorem wBIH_MP ϕ ψ : wBIH_prv (Union _ (Singleton _ ϕ) (clos_DN_eq ϕ ψ)) ψ.
Proof.
eapply wMP.
- eapply wMP.
  + apply wAx ; eapply A6 ; reflexivity.
  + apply wId ; right ; exists 0 ; cbn ; auto.
- apply wId ; left ; split.
Qed.

Theorem wBIH_Re_Top : forall χ, clos_DN_eq ⊤ ⊤ χ -> 
    wBIH_prv (Empty_set _) χ.
Proof.
intros. destruct H as (n & Hn) ; subst.
apply DN_form_rule. eapply wMP.
- eapply wMP.
  + eapply wMP.
    * apply wAx ; eapply A8 ; reflexivity.
    * apply Thm_irrel.
  + apply Thm_irrel.
- apply prv_Top.
Qed.

Theorem wBIH_Re_Bot : forall χ, clos_DN_eq ⊥ ⊥ χ -> 
    wBIH_prv (Empty_set _) χ.
Proof.
intros. destruct H as (n & Hn) ; subst.
apply DN_form_rule. eapply wMP.
- eapply wMP.
  + eapply wMP.
    * apply wAx ; eapply A8 ; reflexivity.
    * apply wBIH_Deduction_Theorem ; apply imp_Id_gen.
  + apply wBIH_Deduction_Theorem ; apply imp_Id_gen.
- apply prv_Top.
Qed.

Theorem wBIH_Re_And ϕ1 ϕ2 ψ1 ψ2 : forall χ, clos_DN_eq (ϕ1 ∧ ϕ2) (ψ1 ∧ ψ2) χ -> 
    wBIH_prv (Union _ (clos_DN_eq ϕ1 ψ1) (clos_DN_eq ϕ2 ψ2)) χ.
Proof.
intros χ (n & H) ; subst.
apply wMP with (DN_form n (ϕ2 <--> ψ2)).
- apply wMP with (DN_form n (ϕ1 <--> ψ1)).
  + apply wBIH_comp with (Empty_set _).
    * apply meta_Imp_trans with (DN_form n ((ϕ2 <--> ψ2) --> (ϕ1 ∧ ϕ2 <--> ψ1 ∧ ψ2))).
      -- eapply wMP.
        ++ apply DN_form_dist_imp.
        ++ apply DN_form_rule. apply wBIH_Deduction_Theorem.
           apply wBIH_Deduction_Theorem. eapply wMP ; [ | apply prv_Top].
           eapply wMP.
           ** eapply wMP.
             --- apply wAx ; eapply A8 ; reflexivity.
             --- apply wBIH_Deduction_Theorem. eapply wMP.
               +++ eapply wMP.
                 *** apply wAx ; eapply A8 ; reflexivity.
                 *** eapply meta_Imp_trans.
                   ---- apply wAx ; eapply A6 ; reflexivity.
                   ---- eapply wMP.
                     ++++ apply wAx ; eapply A6 ; reflexivity.
                     ++++ apply wId ; left ; left ; right ; split.
               +++ eapply meta_Imp_trans.
                 *** apply wAx ; eapply A7 ; reflexivity.
                 *** eapply wMP.
                   ---- apply wAx ; eapply A6 ; reflexivity.
                   ---- apply wId ; left ; right ; split.
           ** apply wBIH_Deduction_Theorem. eapply wMP.
             --- eapply wMP.
               +++ apply wAx ; eapply A8 ; reflexivity.
               +++ eapply meta_Imp_trans.
                *** apply wAx ; eapply A6 ; reflexivity.
                *** eapply wMP.
                  ---- apply wAx ; eapply A7 ; reflexivity.
                  ---- apply wId ; left ; left ; right ; split.
             --- eapply meta_Imp_trans.
                 *** apply wAx ; eapply A7 ; reflexivity.
                 *** eapply wMP.
                   ---- apply wAx ; eapply A7 ; reflexivity.
                   ---- apply wId ; left ; right ; split.
      -- apply DN_form_dist_imp.
    * intros B HB ; inversion HB.
  + apply wId ; left ; exists n ; auto.
- apply wId ; right ; exists n ; auto.
Qed.

Theorem wBIH_Re_Or ϕ1 ϕ2 ψ1 ψ2 : forall χ, clos_DN_eq (ϕ1 ∨ ϕ2) (ψ1 ∨ ψ2) χ -> 
    wBIH_prv (Union _ (clos_DN_eq ϕ1 ψ1) (clos_DN_eq ϕ2 ψ2)) χ.
Proof.
intros χ (n & H) ; subst.
apply wMP with (DN_form n (ϕ2 <--> ψ2)).
- apply wMP with (DN_form n (ϕ1 <--> ψ1)).
  + apply wBIH_comp with (Empty_set _).
    * apply meta_Imp_trans with (DN_form n ((ϕ2 <--> ψ2) --> (ϕ1 ∨ ϕ2 <--> ψ1 ∨ ψ2))).
      -- eapply wMP.
        ++ apply DN_form_dist_imp.
        ++ apply DN_form_rule. apply wBIH_Deduction_Theorem.
           apply wBIH_Deduction_Theorem. eapply wMP ; [ | apply prv_Top].
           eapply wMP.
           ** eapply wMP.
             --- apply wAx ; eapply A8 ; reflexivity.
             --- apply wBIH_Deduction_Theorem. eapply wMP.
               +++ eapply wMP.
                 *** apply wAx ; eapply A5 ; reflexivity.
                 *** eapply meta_Imp_trans.
                   ---- eapply wMP.
                     ++++ apply wAx ; eapply A6 ; reflexivity.
                     ++++ apply wId ; left ; left ; right ; split.
                   ---- apply wAx ; eapply A3 ; reflexivity.
               +++ eapply meta_Imp_trans.
                 *** eapply wMP.
                   ---- apply wAx ; eapply A6 ; reflexivity.
                   ---- apply wId ; left ; right ; split.
                 *** apply wAx ; eapply A4 ; reflexivity.
           ** apply wBIH_Deduction_Theorem. eapply wMP.
             --- eapply wMP.
               +++ apply wAx ; eapply A5 ; reflexivity.
               +++ eapply meta_Imp_trans.
                *** eapply wMP.
                  ---- apply wAx ; eapply A7 ; reflexivity.
                  ---- apply wId ; left ; left ; right ; split.
                *** apply wAx ; eapply A3 ; reflexivity.
             --- eapply meta_Imp_trans.
                 *** eapply wMP.
                   ---- apply wAx ; eapply A7 ; reflexivity.
                   ---- apply wId ; left ; right ; split.
                 *** apply wAx ; eapply A4 ; reflexivity.
      -- apply DN_form_dist_imp.
    * intros B HB ; inversion HB.
  + apply wId ; left ; exists n ; auto.
- apply wId ; right ; exists n ; auto.
Qed.

Theorem wBIH_Re_Imp ϕ1 ϕ2 ψ1 ψ2 : forall χ, clos_DN_eq (ϕ1 --> ϕ2) (ψ1 --> ψ2) χ -> 
    wBIH_prv (Union _ (clos_DN_eq ϕ1 ψ1) (clos_DN_eq ϕ2 ψ2)) χ.
Proof.
intros χ (n & H) ; subst.
apply wMP with (DN_form n (ϕ2 <--> ψ2)).
- apply wMP with (DN_form n (ϕ1 <--> ψ1)).
  + apply wBIH_comp with (Empty_set _).
    * apply meta_Imp_trans with (DN_form n ((ϕ2 <--> ψ2) --> ((ϕ1 --> ϕ2) <--> (ψ1 --> ψ2)))).
      -- eapply wMP.
        ++ apply DN_form_dist_imp.
        ++ apply DN_form_rule. repeat apply wBIH_Deduction_Theorem.
           eapply wMP ; [ | apply prv_Top].
           eapply wMP.
           ** eapply wMP.
             --- apply wAx ; eapply A8 ; reflexivity.
             --- repeat apply wBIH_Deduction_Theorem. apply wMP with ϕ2.
               +++ eapply wMP.
                 *** apply wAx ; eapply A6 ; reflexivity.
                 *** apply wId ; left ; left ; left ; right ; split.
               +++ eapply wMP.
                 *** apply wId ; left ; right ; split.
                 *** apply wBIH_Detachment_Theorem.
                     eapply wMP.
                  ---- apply wAx ; eapply A7 ; reflexivity.
                  ---- apply wId ; left ; left ; left ; right ; split.
           ** repeat apply wBIH_Deduction_Theorem. apply wMP with ψ2.
             --- eapply wMP.
               +++ apply wAx ; eapply A7 ; reflexivity.
               +++ apply wId ; left ; left ; left ; right ; split.
             --- eapply wMP.
               +++ apply wId ; left ; right ; split.
               +++ apply wBIH_Detachment_Theorem. eapply wMP.
                 *** apply wAx ; eapply A6 ; reflexivity.
                 *** apply wId ; left ; left ; left ; right ; split.
      -- apply DN_form_dist_imp.
    * intros B HB ; inversion HB.
  + apply wId ; left ; exists n ; auto.
- apply wId ; right ; exists n ; auto.
Qed.

Axiom LEM : forall P, P \/ ~ P.

Theorem wBIH_Re_Excl ϕ1 ϕ2 ψ1 ψ2 : forall χ, clos_DN_eq (ϕ1 --< ϕ2) (ψ1 --< ψ2) χ -> 
    wBIH_prv (Union _ (clos_DN_eq ϕ1 ψ1) (clos_DN_eq ϕ2 ψ2)) χ.
Proof.
intros χ (n & H) ; subst.
apply wMP with (DN_form (S n) (ϕ2 <--> ψ2)).
- apply wMP with (DN_form (S n) (ϕ1 <--> ψ1)).
  + apply wBIH_comp with (Empty_set _).
    * apply meta_Imp_trans with (DN_form n ((¬ ∞ (ϕ2 <--> ψ2)) --> ((ϕ1 --< ϕ2) <--> (ψ1 --< ψ2)))).
      -- apply meta_Imp_trans with (DN_form n (¬ ∞ (ϕ1 <--> ψ1))).
        ++ rewrite DN_form_S. eapply imp_Id_gen.
        ++ eapply wMP.
          ** apply DN_form_dist_imp.
          ** apply DN_form_rule. repeat apply wBIH_Deduction_Theorem.
             eapply wMP ; [ | apply prv_Top]. eapply wMP.
             --- eapply wMP.
               +++ apply wAx ; eapply A8 ; reflexivity.
               +++ apply wBIH_Deduction_Theorem.
                   (* There must exist a syntactic proof, but the Kripke
                      semantics argument is rather straightforward. *)
                   apply wCompleteness.
                   intros M w H v wRv Hv H0. apply Hv ; intros u uRv Hu.
                   assert (wforces M v (¬ (∞ (ϕ1 <--> ψ1)))).
                   apply Persistence with w ; auto. apply H ; left ; left ; right ; split.
                   assert (wforces M v (¬ (∞ (ϕ2 <--> ψ2)))).
                   apply Persistence with w ; auto. apply H ; left ; right ; split.
                   assert (wforces M u (ϕ2 <--> ψ2)).
                   { destruct (LEM (wforces M u (ϕ2 <--> ψ2))) as [H3 | H3] ; [exact H3 | exfalso].
                     apply (H2 v (@reach_refl _ _)). intro H4.
                     destruct (H4 u uRv I). apply H3 ; split ; auto. }
                   apply H3 ; [apply reach_refl | ].
                   apply H0 ; auto.
                   destruct (LEM (wforces M u ψ1)) as [H4 | H4] ; [exact H4 | exfalso].
                   apply (H1 v (@reach_refl _ _)). intro H5.
                   destruct (H5 u uRv I). apply H4 ; apply H6 ; [apply reach_refl | auto].
             --- apply wBIH_Deduction_Theorem.
                   (* There must exist a syntactic proof, but the Kripke
                      semantics argument is rather straightforward. *)
                 apply wCompleteness.
                 intros M w H v wRv Hv H0. apply Hv ; intros u uRv Hu.
                 assert (wforces M v (¬ (∞ (ϕ1 <--> ψ1)))).
                 apply Persistence with w ; auto. apply H ; left ; left ; right ; split.
                 assert (wforces M v (¬ (∞ (ϕ2 <--> ψ2)))).
                 apply Persistence with w ; auto. apply H ; left ; right ; split.
                 assert (wforces M u (ϕ2 <--> ψ2)).
                 { destruct (LEM (wforces M u (ϕ2 <--> ψ2))) as [H3 | H3] ; [exact H3 | exfalso].
                   apply (H2 v (@reach_refl _ _)). intro H4.
                   destruct (H4 u uRv I). apply H3 ; split ; auto. }
                 apply H3 ; [apply reach_refl | ].
                 apply H0 ; auto.
                 destruct (LEM (wforces M u ϕ1)) as [H4 | H4] ; [exact H4 | exfalso].
                 apply (H1 v (@reach_refl _ _)). intro H5.
                 destruct (H5 u uRv I). apply H4 ; apply H7 ; [apply reach_refl | auto].
      -- rewrite DN_form_S. apply DN_form_dist_imp.
    * intros B HB ; inversion HB.
  + apply wId ; left ; exists (S n) ; auto.
- apply wId ; right ; exists (S n) ; auto.
Qed.

End equivalential.












Section not_finitely_equivalential.

Definition Even n := exists m, n = 2*m.
Definition Odd n := exists m, n = 2*m+1.

Lemma Even_Odd_dec : forall m, Even m \/ Odd m.
Proof.
induction m.
- left ; exists 0 ; lia.
- destruct IHm.
  + right. destruct H ; subst. cbn. exists x ; lia.
  + left. destruct H ; subst. cbn. exists (S x) ; lia.
Qed.

Lemma wforces_DN_form_le : forall m n M w A, n <= m ->
  (wforces M w (DN_form m A)) -> (wforces M w (DN_form n A)).
Proof.
induction m ; cbn.
- intros. inversion H ; subst. cbn ; auto.
- intros. inversion H.
  + subst. cbn. auto.
  + subst. apply IHm ; auto.
    destruct (LEM (wforces M w (DN_form m A))) as [H' | H'] ; [exact H' | exfalso ].
    apply H0 with w ; [ apply reach_refl | ]. intro. apply H'.
    apply H1 ; auto. apply reach_refl.
Qed.

Lemma head_n_reachable : forall n M w v u r,
  reachable w v -> reachable u v -> n_reachable M n u r ->
  n_reachable M (S (S n)) w r.
Proof.
induction n.
- intros. cbn in H1 ; subst. exists v ; split ; auto.
  exists w ; split ; cbn ; auto.
- intros. destruct H1 as (s & Hs0 & Hs1).
  eapply IHn in Hs1. 2: exact H. 2: auto.
  exists s ; split ; auto.
Qed.

Lemma head_n_zz : forall n M w v u r,
  reachable w v -> reachable u v -> n_zz M n u r ->
  n_zz M (S n) w r.
Proof.
induction n.
- intros. cbn in H1 ; subst. cbn. exists w,v ; split ; auto.
- intros. destruct H1 as (s & t & (Hs0 & Hs1) & Hs2).
  exists s,t. repeat split ; auto.
  apply IHn with v u ; auto.
Qed.

Lemma DN_form_n_reachable : forall n M w A,
  (forall m v, m <= 2*n -> (n_reachable M m w v) -> (wforces M v A)) ->
  (wforces M w (DN_form n A)).
Proof.
induction n ; intros M w A H ; auto.
- cbn ; apply H with 0 ; auto ; cbn ; auto.
- cbn. intros v wRv H1. apply H1. intros. clear H1.
  apply IHn. intros. apply H with (S (S m)) ; try lia.
  apply head_n_reachable with v v0 ; auto.
Qed.

Lemma n_reachable_DN_clos : forall M n w A,
  (wforces M w (DN_form n A)) ->
    (forall m v, m <= 2*n -> (n_reachable M m w v) -> (wforces M v A)).
Proof.
induction n.
- intros. cbn in H. inversion H0 ; subst. cbn in H1 ; subst. auto.
- intros. destruct m.
  + cbn in H1 ; subst. apply wforces_DN_form_le with (m:= S n) (n:=0) in H ; try lia.
    cbn in H ; auto.
  + cbn in H1. destruct H1. destruct H1. destruct m.
    * cbn in H2 ; subst.
      cbn in H. destruct H1.
      -- apply wforces_DN_form_le with (m:= S n) (n:=0) in H ; try lia.
         cbn in H. apply Persistence with x ; auto.
      -- apply wforces_DN_form_le with (m:= S n) (n:=1) in H ; try lia.
         destruct (LEM (wforces M v A)) as [H' | H'] ; [exact H' | exfalso ].
         cbn in H. apply H with x ; [ apply reach_refl | ]. intro H2.
         apply H'. apply H2 ; auto.
    * cbn in H2. destruct H2. destruct H2. apply IHn with (A:=DN_form 1 A) in H3 ; auto.
      -- destruct (LEM (wforces M v A)) as [H' | H'] ; [exact H' | exfalso ].
         destruct H1.
         ++ destruct H2.
          ** apply H' ; apply Persistence with x0.
             apply wforces_DN_form_le with (n:= 0) (m:=1) in H3 ; try lia.
             cbn in H3 ; auto.
             apply reach_tran with x ; auto.
          ** apply H3 with x0 ; [apply reach_refl | ]. intro.
             apply H'. apply Persistence with x ; auto.
             apply H4 ; auto.
         ++ destruct H2.
          ** apply H3 in H2. apply H2. intros H4. apply H' ; apply H4 ; auto.
          ** apply H3 with x0 ; [apply reach_refl | ]. intro.
             apply H'. apply H4 ; auto. apply reach_tran with x ; auto.
      -- apply wforces_DN_form_le with n ; auto. cbn ; auto.
         rewrite DN_form_S in H ; auto.
      -- lia.
Qed.

Lemma n_reachable_DN_clos_equiv : forall M n w A,
  (wforces M w (DN_form n A)) <->
    (forall m v, m <= 2*n -> (n_reachable M m w v) -> (wforces M v A)).
Proof.
intros. split ; [ apply n_reachable_DN_clos | apply DN_form_n_reachable].
Qed.

Lemma n_zz_DN_clos_equiv : forall M n w A,
  (wforces M w (DN_form n A)) <->
    (forall v, (n_zz M n w v) -> (wforces M v A)).
Proof.
intros. split.
- intros. apply n_zz_reachable_subset in H0.
  pose (n_reachable_DN_clos _ _ _ _ H (2 * n) v).
  apply w0 ; auto.
- revert n M w A. induction n.
  + cbn ; intros. apply H ; auto.
  + intros. cbn. intros. apply H1. intros.
    clear H3. clear H1.
    apply IHn. intros. apply H.
    apply head_n_zz with v v0 ; auto.
Qed.
  
Variable n: nat.

Definition finclos_DN_eq ϕ ψ χ : Prop := exists m, m <= n /\ χ = DN_form m (ϕ <--> ψ).

Definition Xmas_lights : model.
Proof.
unshelve eapply (@Build_model).
(* Nodes *)
- exact nat.
(* Relation *)
- exact (fun x y => x = y \/ (Odd y /\ ((x = S y) \/ (y = S x)))).
(* Valuation function *)
- exact (fun x p => (Odd x) \/ (Even x /\ x <= 2*n) \/ (x = 2*(S n) /\ (p = 1))).
(* Reflexivity *)
- intros ; cbn ; auto.
(* Transitivity *)
- cbn ; intros. destruct H,H0 ; subst ; auto. destruct H. destruct H1 ; subst ; auto.
  + destruct H0. destruct H1 ; subst ; auto.
    exfalso. destruct H,H0 ; subst ; lia.
  + destruct H0. destruct H1 ; subst.
    * lia.
    * exfalso. destruct H,H0 ; subst ; lia.
(* Persistence *)
- cbn. intros. destruct H ; subst ; auto. left ; firstorder.
Defined.

Lemma n_reachable_False : forall m n, m < n -> n_reachable Xmas_lights m 0 n -> False.
Proof.
induction m ; cbn ; intros ; subst ; try lia.
destruct H0 as (k & Hk0 & Hk1). destruct Hk0.
- destruct H0 ; subst ; auto.
  + apply IHm with n0 ; auto ; lia.
  + destruct H0. destruct H1 ; subst.
    * apply IHm in Hk1 ; auto ; lia.
    * apply IHm in Hk1 ; auto ; lia.
- destruct H0 ; subst.
  + apply IHm in Hk1 ; auto ; lia.
  + destruct H0. destruct H1 ; subst.
    * apply IHm in Hk1 ; auto ; lia.
    * apply IHm in Hk1 ; auto ; lia.
Qed.

Lemma n_reachable_Xmas_Id : forall m, n_reachable Xmas_lights m 0 m.
Proof.
induction m ; cbn ; intros ; subst ; try lia.
exists m. split ; auto.
destruct (Even_Odd_dec m).
- left. right ; split ; auto.
  destruct H ; subst ; cbn. exists x ; lia.
- right. right ; split ; auto.
Qed.

Lemma n_reachable_finclos_DN_13 : forall m v, m <= 2*n ->
   (n_reachable Xmas_lights m 0 v) -> (wforces Xmas_lights v (#1 <--> #3)). 
Proof.
apply (well_founded_induction_type lt_wf (fun m => 
forall (v : nodes), m <= 2*n -> n_reachable Xmas_lights m 0 v ->
wforces Xmas_lights v (#1 <--> #3))).
intros. split ; intros u Hu1 Hu2.
- destruct Hu1 ; subst.
  + destruct Hu2 ; [ left ; auto | ]. destruct H2 ; subst.
    * destruct H2. right. left ; auto.
    * destruct H2 ; subst. destruct x ; cbn in H1 ; try lia.
      destruct H1. destruct H1. assert (2 * S n =(S (n + S (n + 0)))). lia.
      rewrite <- H4 in H1 ; clear H4. destruct H1.
      -- destruct H1 ; subst ; try lia.
        ++ exfalso. clear H. apply n_reachable_False in H2 ; auto. lia.
        ++ left ; firstorder.
      -- destruct H1 ; subst.
        ++ exfalso ; apply n_reachable_False in H2 ; auto ; lia.
        ++ destruct H1. destruct H4 ; subst.
          ** exfalso ; apply n_reachable_False in H2 ; auto ; lia.
          ** exfalso ; apply n_reachable_False in H2 ; auto ; lia.
  + destruct H2 ; left ; auto.
- destruct Hu1 ; subst.
  + destruct Hu2 ; [ left ; auto | ]. destruct H2 ; subst.
    * destruct H2. right. left ; auto.
    * destruct H2 ; subst. inversion H3.
  + destruct H2 ; left ; auto.
Qed.

Lemma n_reachable_finclos_DN_24 : forall m v, m <= 2*n ->
   (n_reachable Xmas_lights m 0 v) -> (wforces Xmas_lights v (#2 <--> #4)). 
Proof.
apply (well_founded_induction_type lt_wf (fun m => forall  (v : nodes),
m <= 2 * n -> n_reachable Xmas_lights m 0 v -> wforces Xmas_lights v (#2 <--> #4))).
intros. split ; intros u Hu1 Hu2.
- destruct Hu1 ; subst.
  + destruct Hu2 ; [ left ; auto | ]. destruct H2 ; subst.
    * destruct H2. right. left ; auto.
    * destruct H2 ; subst. destruct x ; cbn in H1 ; try lia.
  + destruct H2 ; left ; auto.
- destruct Hu1 ; subst.
  + destruct Hu2 ; [ left ; auto | ]. destruct H2 ; subst.
    * destruct H2. right. left ; auto.
    * destruct H2 ; subst. inversion H3.
  + destruct H2 ; left ; auto.
Qed.

Lemma failure_Xmas_lights : ~ wforces Xmas_lights (2*n) ((# 1 --< # 2) --> (# 3 --< # 4)).
Proof.
intro. apply (H (S (2*n))).
- cbn. right. split.
  + exists n ; lia.
  + lia.
- intro H0. pose (H0 (S (S (2 * n)))). cbn in v.
  destruct v ; try lia.
  + right. split ; auto. exists n. lia.
  + destruct H1 ; lia.
- intros. destruct H0 ; subst.
  + left. cbn. exists n ; lia.
  + destruct H0. destruct H2 ; subst.
    * cbn in H1. destruct H1.
      -- destruct H1 ; lia.
      -- destruct H1.
        ++ destruct H1. destruct H1 ; lia.
        ++ lia.
    * inversion H2 ; subst. right. left. split ; try lia.
      exists n ; lia.
Qed.

Theorem wBIH_Re_Excl_fail : exists χ, finclos_DN_eq (#1 --< #2) (#3 --< #4) χ /\ 
    ~ wBIH_prv (Union _ (finclos_DN_eq #1 #3) (finclos_DN_eq #2 #4)) χ.
Proof.
exists (DN_form n ((#1 --< #2) <--> (#3 --< #4))). split.
- exists n ; split ; auto.
- intro F. apply LEM_wSoundness in F.
  assert (~ wforces Xmas_lights 0 (DN_form n (# 1 --< # 2 <--> # 3 --< # 4))).
  { intro. apply n_reachable_DN_clos with (v:=2*n) (m:=2*n) in H ; try lia.
    - apply failure_Xmas_lights. destruct H ; auto.
    - apply n_reachable_Xmas_Id. }
  apply H. apply F. intros. inversion H0 ; subst.
  + inversion H1. destruct H2 ; subst.
    apply DN_form_n_reachable. intros.
    apply n_reachable_finclos_DN_13 with m ; auto ; lia.
  + inversion H1. destruct H2 ; subst.
    apply DN_form_n_reachable. intros.
    apply n_reachable_finclos_DN_24 with m ; auto ; lia.
Qed.

End not_finitely_equivalential.