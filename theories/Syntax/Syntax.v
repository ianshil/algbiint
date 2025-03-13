Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Declare Scope My_scope.
Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.


(* First, let us define propositional formulas. *)

Inductive form : Type :=
 | Var : nat -> form
 | Bot : form
 | Top : form
 | And : form -> form -> form
 | Or : form -> form -> form
 | Imp : form -> form -> form
 | Excl : form -> form -> form.

(* We use the following notations for modal formulas. *)

Notation "# p" := (Var p) (at level 1) : My_scope.
Notation "A --> B" := (Imp A B) (at level 43, right associativity) : My_scope.
Notation "A --< B" := (Excl A B) (at level 43, right associativity) : My_scope.
Notation "A ∨ B" := (Or A B) (at level 42, right associativity) : My_scope.
Notation "A ∧ B" := (And A B) (at level 41, right associativity) : My_scope.
Notation "A <--> B" := ((A --> B) ∧ (B --> A)) (at level 44, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.
Notation "⊤" := (Top) : My_scope.
Notation "¬ A" := (A --> ⊥) (at level 42) : My_scope.
Notation "∞ A" := (⊤ --< A) (at level 42) : My_scope.

(* Next, we define the set of subformulas of a formula, and
    extend this notion to lists of formulas. *)

Fixpoint subform (φ : form) : Ensemble form :=
match φ with
| Var p => Singleton _ (Var p)
| ⊥ => Singleton _ ⊥
| ⊤ => Singleton _ ⊤
| ψ ∧ χ => Union _ (Singleton _ (ψ ∧ χ)) (Union _ (subform ψ) (subform χ))
| ψ ∨ χ => Union _ (Singleton _ (ψ ∨ χ)) (Union _ (subform ψ) (subform χ))
| ψ --> χ => Union _ (Singleton _ (ψ --> χ)) (Union _ (subform ψ) (subform χ))
| ψ --< χ => Union _ (Singleton _ (ψ --< χ)) (Union _ (subform ψ) (subform χ))
end.

Fixpoint subformlist (φ : form) : list form :=
match φ with
| Var p => (Var p) :: nil
| ⊥ => [⊥]
| ⊤ => [⊤]
| ψ ∧ χ => (ψ ∧ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ ∨ χ => (ψ ∨ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ --> χ => (ψ --> χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ --< χ => (ψ --< χ) :: (subformlist ψ) ++ (subformlist χ)
end.

(* Equality is decidable over formulas. *)

Lemma eq_dec_form : forall x y : form, {x = y}+{x <> y}.
Proof.
repeat decide equality.
Qed.

(* We define the notion of uniform substitution. *)

Fixpoint subst (σ : nat -> form) (φ : form) : form :=
match φ with
| # p => (σ p)
| ⊥ => ⊥
| ⊤ => ⊤
| ψ ∧ χ => (subst σ ψ) ∧ (subst σ χ)
| ψ ∨ χ => (subst σ ψ) ∨ (subst σ χ)
| ψ --> χ => (subst σ ψ) --> (subst σ χ)
| ψ --< χ => (subst σ ψ) --< (subst σ χ)
end.

Definition first_subst ϕ ψ := subst (fun n => match n with | 0 => ϕ | S n => # (S n) end) ψ.

Lemma first_subst_idem ϕ : ϕ = first_subst #0 ϕ.
Proof.
induction ϕ ; cbn ; unfold first_subst in * ; auto.
2-5: rewrite <- IHϕ1, <- IHϕ2 ; auto.
destruct n ; cbn ; auto.
Qed.

Fixpoint DN_form n A :=
match n with
 | 0 => A
 | S m => ¬ ∞ (DN_form m A)
end.

Inductive DN_clos_set Γ: @Ensemble form :=
  | InitClo : forall A, In _ Γ A -> DN_clos_set Γ A
  | IndClo : forall A,  DN_clos_set Γ A -> DN_clos_set Γ (¬ ∞ A).

Lemma DN_form_S n ϕ : DN_form (S n) ϕ = DN_form n (¬ ∞ ϕ).
Proof.
induction n ; cbn ; auto.
rewrite <- IHn ; cbn ; auto.
Qed.

Lemma In_form_dec : forall l (A : form), {List.In A l} + {List.In A l -> False}.
Proof.
induction l ; simpl ; intros ; auto.
destruct (IHl A) ; auto.
destruct (eq_dec_form a A) ; auto.
right. intro. destruct H ; auto.
Qed.

Fixpoint list_disj (l : list form) : form :=
match l with
 | nil => ⊥
 | h :: t => h ∨ (list_disj t)
end.

Fixpoint list_conj (l : list form) : form :=
match l with
 | nil => ⊤
 | h :: t => h ∧ (list_conj t)
end.

Fixpoint depth (φ : form) : nat :=
match φ with
| Var p => 1
| ⊥ => 1
| ⊤ => 1
| ψ ∧ χ => max (depth ψ) (depth χ)
| ψ ∨ χ => max (depth ψ) (depth χ)
| ψ --> χ => S (max (depth ψ) (depth χ))
| ψ --< χ => S (max (depth ψ) (depth χ))
end.

Lemma depth_zero : forall ϕ, ~ depth ϕ = 0.
Proof.
induction ϕ ; cbn ; lia.
Qed.

