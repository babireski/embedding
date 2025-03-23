Require Import Modal_Library Modal_Notations Modal_Tactics Deductive_System Sets.
Set Implicit Arguments.

Section Translations.
    Context `{X : modal_index_set}.

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

    Fixpoint depth (α : Sentence) : nat :=
    match α with
        | ⊥     => 0
        | #a    => 0
        | φ ∧ ψ => 1 + max (depth φ) (depth ψ)
        | φ ∨ ψ => 1 + max (depth φ) (depth ψ)
        | φ → ψ => 1 + max (depth φ) (depth ψ)
    end.

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
    | A₁ : forall φ ψ,   System (S₁ φ ψ)
    | A₂ : forall φ ψ γ, System (S₂ φ ψ γ)
    | A₃ : forall φ ψ,   System (S₃ φ ψ)
    | A₄ : forall φ ψ,   System (S₄ φ ψ)
    | A₅ : forall φ ψ,   System (S₅ φ ψ)
    | A₆ : forall φ ψ,   System (S₆ φ ψ)
    | A₇ : forall φ ψ,   System (S₇ φ ψ)
    | A₈ : forall φ ψ γ, System (S₈ φ ψ γ)
    | A₉ : forall φ,     System (S₉ φ).

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
    | R₁ : forall (Γ : Theory) (α : Sentence), Γ α -> Deduction Γ α
    | R₂ : forall (Γ : Theory) (a : Schema) (α : Sentence), System a -> instantiate a = α -> Deduction Γ α
    | R₃ : forall (Γ : Theory) (α β : Sentence), Deduction Γ (α → β) -> Deduction Γ α ->  Deduction Γ β.

    Notation "Γ ⊢ α" := (Deduction Γ α) (at level 110, no associativity).

    Notation " ∅ " := Empty.
    Notation " A ∪ B " := (Union A B) (at level 48, left associativity).
    Notation " [ a ] " := (Singleton a) (at level 0, right associativity).

    Theorem union_empty_left : forall {T} (A: T -> Prop) t, A t <-> Union Empty A t.
    Proof.
        intros.
        split.
        + intros. right. assumption.
        + intros. destruct H.
            ++ contradiction.
            ++ assumption.
    Qed.

    Theorem deduction : forall (M : axiom -> Prop) (Γ : theory) (α β : formula), Subset P M -> (M; Γ ∪ [[! α !]] |-- [! β !]) -> M; Γ |-- [! α -> β !].
    Proof.
        intros M Γ α β P H.
        remember (Union Γ (Singleton α)) as Δ eqn: I in H.
        induction H as [ Δ β | Δ A β H₁ H₂ | Δ β γ H₁ H₂ H₃ H₄ | Δ β j H₁ H₂ ].
        + rewrite I in H. destruct H.
            ++ apply Mp with (t := Γ) (f := [! β !]) (g := [! (α -> β) !]).
                +++ apply Ax with (t := Γ) (a := ax1 [! β !] [! α !]) (f := [! β -> α -> β !]).
                    ++++ apply P. apply P_ax1.
                    ++++ simpl. reflexivity.
                +++ apply Prem. assumption.
            ++ rewrite H.
               apply derive_identity.
               unfold Subset.
               intros.
               apply P.
               assumption.
        + apply Mp with (t := Γ) (f := [! β !]) (g := [! α -> β !]).
            ++ apply Ax with (t := Γ) (a := ax1 [! β !] [! α !]) (f := [! β -> α -> β !]).
                +++ apply P. apply P_ax1.
                +++ simpl. reflexivity.
            ++ apply Ax with (t := Γ) (a := A) (f := [! β !]).
                +++ assumption.
                +++ assumption.
        + apply H₂ in I as H₅.
          apply H₄ in I as H₆.
          apply Mp with (t := Γ) (f := [! α -> β !]) (g := [! α -> γ !]).
            ++ apply Mp with (t := Γ) (f := [! α -> β -> γ !]) (g := [! (α -> β) -> α -> γ !]).
                +++ apply Ax with (t := Γ) (a := ax2 [! α !] [! β !] [! γ !]) (f := [! (α -> β -> γ) -> (α -> β) -> α -> γ !]).
                    ++++ apply P. apply P_ax2.
                    ++++ simpl. reflexivity.
                +++ assumption.
            ++ assumption. 
        + apply Mp with (t := Γ) (f := [! [j]β !]) (g := [! α -> [j]β !]).
            ++ apply Ax with (t := Γ) (a := ax1 [! [j]β !] [! α !]) (f := [! [j]β -> α -> [j]β !]).
                +++ apply P. apply P_ax1.
                +++ simpl. reflexivity.
            ++ apply Nec. assumption.
    Qed.

    Fixpoint square (α : Sentence) (i : modal_index) : formula :=
    match α with
        | Contradiction   => [! #1 /\ ~#1 !]
        | Proposition a   => [! [i] #a !]
        | Conjunction ϕ ψ => [! square ϕ i /\ square ψ i !]
        | Disjunction ϕ ψ => [! square ϕ i \/ square ψ i !]
        | Implication ϕ ψ => [! square ϕ i -> square ψ i !]
    end. 

    Fixpoint circle (α : Sentence) (i : modal_index) : formula :=
    match α with
        | Contradiction   => [! #1 /\ ~#1 !]
        | Proposition a   => [! #a !]
        | Conjunction ϕ ψ => [! circle ϕ i /\ circle ψ i !]
        | Disjunction ϕ ψ => [! [i] (circle ϕ i) \/ [i] (circle ψ i) !]
        | Implication ϕ ψ => [! [i] (circle ϕ i) -> circle ψ i !]
    end.

    Theorem equivalence : forall (α : Sentence) i, (S4 i ; Empty |-- Box i (circle α i)) <-> (S4 i ; Empty |-- Box i (square α i)).
    Proof.
    intros.
    split.
    + intros. induction α.
        ++ assumption.
        ++ eapply Nec. assumption.
        ++ admit.
        ++ admit.
        ++ admit.
    + intros. induction α.
        ++ assumption.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
    Admitted.

    Lemma square_nec : forall α i, (S4 i ; Empty |-- square α i) -> (S4 i ; Empty |-- Box i (square α i)).
    Proof.
        intros.
        eapply Nec.
        assumption.
    Qed.
End Translations.