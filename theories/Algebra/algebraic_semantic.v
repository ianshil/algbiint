Require Import List.

Require Import Syntax.
Require Import Bi_Heyting_Algebras.


Section alg_semantics.

Fixpoint interp (A : biHalg) (amap : nat -> nodes) ϕ :=
    match ϕ with
    | # n => amap n
    | ⊥ => zero
    | ⊤ => one
    | ψ ∧ χ => meet (interp A amap ψ) (interp A amap χ)
    | ψ ∨ χ => join (interp A amap ψ) (interp A amap χ)
    | ψ --> χ => rpc (interp A amap ψ) (interp A amap χ)
    | ψ --< χ => subtr (interp A amap ψ) (interp A amap χ)
    end.

(* First, we define the notion of semantic consequence via a set of equations. *)

(* We need to explain how consecutions of equations (pairs of formulas) are
   satisfied in an algebra with an interpretation. *)

Definition alg_eqconseq_eq (Eq : form -> form -> Prop) ϕ ψ := forall A amap,
    (forall χ δ, Eq χ δ -> (interp A amap χ) = (interp A amap δ)) ->
    (interp A amap ϕ) = (interp A amap ψ).

(* Then, we use the notion of satisfiability of equations to intepret consecutions
   of formulas. To do so, we use equations in one place: the variable we use to
   capture this one place is # 0. *)

(* We finally get the consequence relation via equations. This consequence relation
   on bi-Heyting algebras captures sBIL. *)

Definition alg_eqconseq Eq Γ ϕ :=
    forall χ δ, Eq χ δ ->
    alg_eqconseq_eq (fun A B => exists C D, Eq C D /\ exists γ, Γ γ /\ first_subst γ C = A /\ first_subst γ D = B)
    (first_subst ϕ χ) (first_subst ϕ δ).

(* Second, we define the truth-degree preserving consequence relation. This consequence
   relation on bi-Heyting algebras captures wBIL. Note that it builds in a compactness
   result by finitarising Γ (relies on Remark 2.4 of Moraschini's "A gentle introduction
   to the Leibniz hierarchy" (2023)). *)

Definition alg_tdconseq Γ ϕ :=
    exists Γ', (forall γ, Γ' γ -> Γ γ) /\ (exists l, forall γ, List.In γ l <-> Γ' γ) /\
    forall A amap a, (forall γ, Γ' γ -> aleq A a (interp A amap γ)) -> aleq A a (interp A amap ϕ).

(* The usual order consequence relation is as follows. *)

Definition alg_ordconseq Γ ϕ :=
    forall A amap a, (forall γ, Γ γ -> aleq A a (interp A amap γ)) -> aleq A a (interp A amap ϕ).

End alg_semantics.



Section alg_sem_properties.

Lemma first_subst_interp : forall A amap ϕ χ, 
    interp A amap (first_subst χ ϕ) =
    interp A (fun n => match n with | 0 => (interp A amap χ) | _ => amap n end) ϕ.
Proof.
intros A amap ; induction ϕ ; intros ; cbn ; auto.
- cbn. destruct n ; auto.
- rewrite <- IHϕ1. rewrite <- IHϕ2. auto.
- rewrite <- IHϕ1. rewrite <- IHϕ2. auto.
- rewrite <- IHϕ1. rewrite <- IHϕ2. auto.
- rewrite <- IHϕ1. rewrite <- IHϕ2. auto.
Qed.

Lemma DN_form_interp : forall A amap n ϕ, interp A amap (DN_form n ϕ) = DN_alg A n (interp A amap ϕ).
Proof.
intros A amap. induction n.
- intro ϕ ; cbn ; auto.
- intro ϕ ; cbn. rewrite IHn. auto.
Qed.

Lemma list_conj_interp : forall A amap l, interp A amap (list_conj l) = list_meet A (map (interp A amap) l).
Proof.
intros A amap ; induction l ; cbn ; auto.
rewrite IHl ; auto.
Qed.

End alg_sem_properties.

