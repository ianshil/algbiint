Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import gen.

Require Import Syntax.

(* In this file we define two generalised Hilbert calculi based on sets for the propositonal
   bi-intuitionistic logics wBIL and sBIL.  *)

(* We define here the axioms. *)

Inductive Axioms (F : form) : Prop :=
 | A1 A B : F = (A --> (B --> A)) -> Axioms F
 | A2 A B C : F = (A --> (B --> C)) --> ((A --> B) --> (A --> C)) -> Axioms F
 | A3 A B : F = A --> (A ∨ B) -> Axioms F
 | A4 A B : F = B --> (A ∨ B) -> Axioms F
 | A5 A B C : F = (A --> C) --> ((B --> C) --> ((A ∨ B) --> C)) -> Axioms F
 | A6 A B : F = (A ∧ B) --> A -> Axioms F
 | A7 A B : F = (A ∧ B) --> B -> Axioms F
 | A8 A B C : F = (A --> B) --> ((A --> C) --> (A --> (B ∧ C))) -> Axioms F
 | A9 A : F = ⊥ --> A -> Axioms F
 | A10 A : F = A --> ⊤ -> Axioms F
 | BA1 A B : F= A --> (B ∨ (A --< B)) -> Axioms F
 | BA2 A B : F = (A --< B) --> (∞ (A --> B)) -> Axioms F
 | BA3 A B C : F = ((A --< B) --< C) --> (A --< (B ∨ C)) -> Axioms F
 | BA4 A B : F = (¬ (A --< B)) --> (A --> B) -> Axioms F.

(* Finally, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later.

   We start by giving the rules common to both calculi. *)

Inductive wBIH_prv : (form -> Prop) -> form -> Prop :=
  | wId Γ A : In _ Γ A -> wBIH_prv Γ A
  | wAx Γ A : Axioms A -> wBIH_prv Γ A
  | wMP Γ A B : wBIH_prv Γ (A --> B) ->  wBIH_prv Γ A -> wBIH_prv Γ B
  | wDN Γ A : wBIH_prv (Empty_set _) A ->  wBIH_prv Γ (¬ ∞ A).

Inductive sBIH_prv : (form -> Prop) -> form -> Prop :=
  | sId Γ A : In _ Γ A -> sBIH_prv Γ A
  | sAx Γ A : Axioms A -> sBIH_prv Γ A
  | sMP Γ A B : sBIH_prv Γ (A --> B) ->  sBIH_prv Γ A -> sBIH_prv Γ B
  | sDN Γ A : sBIH_prv Γ A ->  sBIH_prv Γ (¬ ∞ A).

(* Define the general notion of derivable pair. *)

Definition wpair_der Γ Δ : Prop :=
    exists (l : list form), NoDup l /\ (forall A, List.In A l -> Δ A) /\
        wBIH_prv Γ (list_disj l).

Definition spair_der Γ Δ : Prop :=
    exists (l : list form), NoDup l /\ (forall A, List.In A l -> Δ A) /\
        sBIH_prv Γ (list_disj l).

Definition complete Γ Δ : Prop :=
    forall (A : form), Γ A \/ Δ A.


