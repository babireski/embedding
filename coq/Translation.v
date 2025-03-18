Require Import Modal_Library Modal_Notations.
Set Implicit Arguments.

Section Translations.
    Context `{X : modal_index_set}.

    Section Intuitionistic.
        Definition Counting := nat.

        Inductive Sentence : Set :=
        | Contradiction : Sentence
        | Proposition   : Counting -> Sentence
        | Conjunction   : Sentence -> Sentence -> Sentence
        | Disjunction   : Sentence -> Sentence -> Sentence
        | Implication   : Sentence -> Sentence -> Sentence.

        Notation " ⊥ "     := Contradiction.
        Notation " # a "   := (Proposition a) (at level 2, no associativity, a constr at level 1, format "# a").
        Notation " ¬ α "   := (Implication α ⊥) (at level 9, right associativity, format "¬ α").
        Notation " α → β " := (Implication α β) (at level 13, right associativity).
        Notation " α ∧ β " := (Conjunction α β) (at level 11, left associativity).
        Notation " α ∨ β " := (Disjunction α β) (at level 12, left associativity).

        Definition Theory := Sentence -> Prop.

        Inductive Schema : Type :=
        | S₁ : Sentence -> Sentence -> Schema
        | S₂ : Sentence -> Sentence -> Sentence -> Schema
        | S₃ : Sentence -> Sentence -> Schema
        | S₄ : Sentence -> Sentence -> Schema
        | S₅ : Sentence -> Sentence -> Schema
        | S₆ : Sentence -> Sentence -> Schema
        | S₇ : Sentence -> Sentence -> Schema
        | S₈ : Sentence -> Sentence -> Sentence -> Schema
        | S₉ : Sentence -> Schema.

        Inductive System : Schema -> Prop :=
        | A₁: forall φ ψ,   System (S₁ φ ψ)
        | A₂: forall φ ψ γ, System (S₂ φ ψ γ)
        | A₃: forall φ ψ,   System (S₃ φ ψ)
        | A₄: forall φ ψ,   System (S₄ φ ψ)
        | A₅: forall φ ψ,   System (S₅ φ ψ)
        | A₆: forall φ ψ,   System (S₆ φ ψ)
        | A₇: forall φ ψ,   System (S₇ φ ψ)
        | A₈: forall φ ψ γ, System (S₈ φ ψ γ)
        | A₉: forall φ,     System (S₉ φ).

        Definition instantiate (a : Schema) : Sentence :=
        match a with
            | S₁ α β   => α → β → α
            | S₂ α β γ => (α → β → γ) → (α → β) → α → γ
            | S₃ α β   => α → β → α ∧ β
            | S₄ α β   => α ∧ β → α
            | S₅ α β   => α ∧ β → β
            | S₆ α β   => α → α ∨ β
            | S₇ α β   => β → α ∨ β
            | S₈ α β γ => (α → γ) → (β → γ) → α ∨ β → γ 
            | S₉ α     => ⊥ → α
        end.

        Inductive Deduction : Theory -> Sentence -> Prop :=
        | Premise : forall (Γ : Theory) (α : Sentence), Γ α -> Deduction Γ α
        | Axioms  : forall (Γ : Theory) (a : Schema) (α : Sentence), System a -> instantiate a = α -> Deduction Γ α
        | Ponens  : forall (Γ : Theory) (α β : Sentence), Deduction Γ (α → β) -> Deduction Γ α ->  Deduction Γ β.

        Notation "Γ ⊢ α" := (Deduction Γ α) (at level 110, no associativity).
    End Intuitionistic.

    Section Deduction.
        Notation "Γ ⊢ α" := (Deduction Γ α) (at level 110, no associativity).
        Theorem Γ ⊢ α → β -->
    End Deduction.

    Section Translation.
        Definition square (α : Sentence) (i : modal_index) : formula :=
        match α with
            | Contradiction   => [! #1 /\ ~#1 !]
            | Proposition a   => [! [i] #a !]
            | Conjunction ϕ ψ => [! square ϕ i /\ square ψ i !]
            | Disjunction ϕ ψ => [! square ϕ i \/ square ψ i !]
            | Implication ϕ ψ => [! square ϕ i -> square ψ i !]
        end. 
    End Translation.
End Translations.

(* Inductive Deduction (A : Schema -> Sentence) : Theory -> Sentence -> Prop :=
| Premise : forall (Γ : Theory) (α : Sentence), Γ α -> Deduction A Γ α
| Axioms  : forall (Γ : Theory) (a : Schema) (α : Sentence), A a -> instantiates a = α -> Deduction A Γ α
| Ponens  : forall (Γ : Theory) (α β : Sentence), Deduction A Γ (α -> β) -> Deduction A Γ α ->  Deduction A Γ β.

End Intuitionistic.

Section Translation.



Definition square (α : Prop) : formula :=
match α with
    | 
    | _ => [!#1!]
end. *)
