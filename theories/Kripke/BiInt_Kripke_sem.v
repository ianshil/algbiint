Require Import List.
Export ListNotations.

Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Syntax.

Section Kripke_semantics.

    Class model :=
      {
        nodes : Type ;
        reachable : nodes -> nodes -> Prop ;
        val : nodes -> nat -> Prop ;

        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

        persist :  forall u v, reachable u v -> forall p, val u p -> val v p;
      }.

Fixpoint wforces (M : model) w A : Prop :=
  match A with
  | Var p => val w p
  | Bot => False
  | Top => True
  | And A B => (wforces M w A) /\ (wforces M w B)
  | Or A B => (wforces M w A) \/ (wforces M w B)
  | Imp A B => forall v, reachable w v -> wforces M v A -> wforces M v B
  | Excl A B => ~ forall v, reachable v w -> wforces M v A -> wforces M v B
  end.

Definition mforces M A : Prop := forall w, wforces M w A.

Definition valid_form A := forall M, mforces M A.

Definition loc_conseq Γ A :=
  forall M w, (forall B, Γ B -> wforces M w B) -> wforces M w A.

Definition glob_conseq Γ A :=
  forall M, (forall B, (In _ Γ B) -> mforces M B) -> mforces M  A.

Lemma Persistence : forall A M w, wforces M w A ->
            (forall v, reachable w v -> wforces M v A).
Proof.
induction A ; intros ; try auto.
- simpl. pose ((@persist M) w v).
  pose (v0 H0 n). apply v1. auto.
- simpl. split. inversion H. apply IHA1 with (w:=w) ; auto.
  inversion H. apply IHA2 with (w:=w) ; auto.
- simpl. inversion H. left. apply IHA1 with (w:=w) ; auto.
  right. apply IHA2 with (w:=w) ; auto.
- simpl. intros. simpl in H. apply H with (v:=v0) ; auto.
  pose ((@reach_tran) _ _ _ _ H0 H1). auto.
- simpl. simpl in H. intro. apply H. intros v' H3. apply H1.
  now apply reach_tran with w.
Qed.

End Kripke_semantics.