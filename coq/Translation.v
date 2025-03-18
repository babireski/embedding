Require Import Modal_Library Modal_Notations.
Set Implicit Arguments.

Section Intuitionistic.

Definition Counting := nat.

Inductive Sentence : Set :=
| Contradiction : Sentence
| Proposition   : Counting -> Sentence
| Negation      : Sentence -> Sentence
| Conjunction   : Sentence -> Sentence -> Sentence
| Disjunction   : Sentence -> Sentence -> Sentence
| Implication   : Sentence -> Sentence -> Sentence.

Notation " ⊥ "     := Contradiction.
Notation " # a "   := (Proposition a) (at level 2, no associativity, a constr at level 1, format "# a").
Notation " ¬ α "   := (Negation α) (at level 9, right associativity, format "¬ α").
Notation " α → β " := (Implication α β) (at level 13, right associativity).
Notation " α ∧ β " := (Conjunction α β) (at level 11, left associativity).
Notation " α ∨ β " := (Disjunction α β) (at level 12, left associativity).

Definition Theory   := Sentence -> Prop. 

Inductive Schema : Type :=
| A₁ : Sentence -> Sentence -> Schema
| A₂ : Sentence -> Sentence -> Sentence -> Schema
| A₃ : Sentence -> Sentence -> Schema
| A₄ : Sentence -> Sentence -> Schema
| A₅ : Sentence -> Sentence -> Schema
| A₆ : Sentence -> Sentence -> Schema
| A₇ : Sentence -> Sentence -> Schema
| A₈ : Sentence -> Sentence -> Sentence -> Schema
| A₉ : Sentence -> Schema.

Definition instantiate (a : Schema) : Sentence :=
match a with
    | A₁ α β   => α → β → α
    | A₂ α β γ => (α → β → γ) → (α → β) → α → γ
    | A₃ α β   => α → β → α ∧ β
    | A₄ α β   => α ∧ β → α
    | A₅ α β   => α ∧ β → β
    | A₆ α β   => α → α ∨ β
    | A₇ α β   => β → α ∨ β
    | A₈ α β γ => (α → γ) → (β → γ) → α ∨ β → γ 
    | A₉ α     => ⊥ → α
end.

(* Inductive Deduction (A : Schema -> Sentence) : Theory -> Sentence -> Prop :=
| Premise : forall (Γ : Theory) (α : Sentence), Γ α -> Deduction A Γ α
| Axioms  : forall (Γ : Theory) (a : Schema) (α : Sentence), A a -> instantiates a = α -> Deduction A Γ α
| Ponens  : forall (Γ : Theory) (α β : Sentence), Deduction A Γ (α -> β) -> Deduction A Γ α ->  Deduction A Γ β.

End Intuitionistic.

Section Translation.

Context `{X : modal_index_set}.

Definition square (α : Prop) : formula :=
match α with
    | 
    | _ => [!#1!]
end. *)