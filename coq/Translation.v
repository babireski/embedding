Require Import Modal_Library Modal_Notations Modal_Tactics Deductive_System Sets Completeness List.
Set Implicit Arguments.

Section Translations.
    Context `{X : modal_index_set}.

    Inductive Sentence : Set :=
    | Contradiction : Sentence
    | Proposition   : nat      -> Sentence
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

    (* Inductive Schema : Type :=
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
    | R₃ : forall (Γ : Theory) (α β : Sentence), Deduction Γ (α → β) -> Deduction Γ α ->  Deduction Γ β. *)

    Inductive Deduction : Theory -> Sentence -> Prop :=
    | R₁ : forall (Γ : Theory) (α : Sentence), Γ α -> Deduction Γ α
    | A₁ : forall Γ α β,   Deduction Γ (α → β → α)
    | A₂ : forall Γ α β γ, Deduction Γ ((α → β → γ) → (α → β) → α → γ)
    | A₃ : forall Γ α β,   Deduction Γ (α → β → α ∧ β)
    | A₄ : forall Γ α β,   Deduction Γ (α ∧ β → α)
    | A₅ : forall Γ α β,   Deduction Γ (α ∧ β → β)
    | A₆ : forall Γ α β,   Deduction Γ (α → α ∨ β)
    | A₇ : forall Γ α β,   Deduction Γ (β → α ∨ β)
    | A₈ : forall Γ α β γ, Deduction Γ ((α → γ) → (β → γ) → α ∨ β → γ )
    | A₉ : forall Γ α,     Deduction Γ (⊥ → α)
    | R₃ : forall (Γ : Theory) (α β : Sentence), Deduction Γ (α → β) -> Deduction Γ α ->  Deduction Γ β.

    Notation "Γ ⊢ α" := (Deduction Γ α) (at level 110, no associativity).

    Notation " ∅ " := Empty.
    Notation " A ∪ B " := (Union A B) (at level 48, left associativity).
    Notation " [ a ] " := (Singleton a) (at level 0, right associativity).

    Theorem deduction : forall (M : axiom -> Prop) (Γ : theory) (α β : formula), Subset P M -> (M; Γ ∪ [[! α !]] |-- [! β !]) -> M; Γ |-- [! α -> β !].
    Proof.
        intros M Γ α β P H.
        remember (Union Γ (Singleton α)) as Δ eqn: I in H.
        induction H as [ Δ β | Δ A β H₁ H₂ | Δ β γ H₁ H₂ H₃ H₄ | Δ β j H₁ H₂ ].
        + rewrite I in H. destruct H.
            ++ apply Mp with [! β !].
                +++ apply Ax with (ax1 [! β !] [! α !]).
                    ++++ apply P. apply P_ax1.
                    ++++ simpl. reflexivity.
                +++ apply Prem. assumption.
            ++ rewrite H.
               apply derive_identity.
               unfold Subset.
               intros.
               apply P.
               assumption.
        + apply Mp with [! β !].
            ++ apply Ax with (ax1 [! β !] [! α !]).
                +++ apply P. apply P_ax1.
                +++ simpl. reflexivity.
            ++ apply Ax with A.
                +++ assumption.
                +++ assumption.
        + apply H₂ in I as H₅.
          apply H₄ in I as H₆.
          apply Mp with [! α -> β !].
            ++ apply Mp with [! α -> β -> γ !].
                +++ apply Ax with (ax2 [! α !] [! β !] [! γ !]).
                    ++++ apply P. apply P_ax2.
                    ++++ simpl. reflexivity.
                +++ assumption.
            ++ assumption. 
        + apply Mp with [! [j]β !].
            ++ apply Ax with (ax1 [! [j]β !] [! α !]).
                +++ apply P. apply P_ax1.
                +++ simpl. reflexivity.
            ++ apply Nec. assumption.
    Qed.

    Inductive Boxed (Γ : theory) (i : modal_index): formula -> Prop :=
    | Boxing : forall α, Γ α -> Boxed Γ i [! [i]α !].

    Lemma boxing : forall Γ α i, (Boxed Γ i) α -> exists φ, α = [! [i]φ !].
    Proof.
        intros. destruct H. exists α. reflexivity.
    Qed.

    Lemma fin_empty_is_empty : forall (α : formula), (Fin [] α) -> (∅ α).
    Proof.
        intros.
        simpl in H.
        contradiction.
    Qed.

    Lemma Boxed_fin_empty_is_empty : forall (α : formula) i, (Boxed (Fin []) i α) -> (∅ α).
    Proof.
        intros.
        apply fin_empty_is_empty.
        inversion H.
        contradiction.
    Qed.

    Theorem subset : forall Δ (α : formula), Subset (Fin Δ) (Fin (α :: Δ)).
    Proof.
        intros Δ α β H.
        right. assumption.
    Qed.

    Theorem union : forall M Δ α β, (M; (Fin (β :: Δ)) |-- α) -> (M; Fin Δ ∪ [β] |-- α).
    Proof.
        intros. inversion H.
        + destruct H0.
            ++ rewrite H0. apply Prem. right. reflexivity.
            ++ apply Prem. left. assumption.
        + apply Ax with a.
            ++ assumption.
            ++ assumption.
        + apply Mp with f.
            ++ admit.
            ++ admit.
        + apply Nec. assumption.
    Admitted.

    Theorem nec_gen : forall (M : axiom -> Prop) Γ (α : formula) i, Subset (K4 i) M -> (M; Boxed Γ i |-- [! α !]) -> M; Boxed Γ i |-- [! [i]α !].
    Proof.
        intros M Γ α i H₁ H₂.
        apply finite_world in H₂.
        destruct H₂ as [Δ H₂ H₃].
        generalize dependent α.
        induction Δ as [ | β Δ H₄].
        + intros. apply Nec. apply derive_weak with (Boxed (Fin []) i).
            ++ intros β H2. apply Boxed_fin_empty_is_empty with i. assumption.
            ++ apply derive_weak with (Fin []).
                +++ intros a B. apply fin_empty_is_empty in B. contradiction.
                +++ assumption.
        + intros α H₅. assert (Boxed Γ i β).
            ++ apply H₃. left. reflexivity.
            ++ apply boxing in H. destruct H. apply Mp with [! [i][i]x !].
                +++ apply Mp with [! [i]([i]x -> α) !].
                    ++++ apply Ax with (axK i [! [i]x !] α).
                        +++++ apply H₁. apply K4_K. apply K_axK.
                        +++++ reflexivity.
                    ++++ apply H₄.
                        +++++ intros γ J. apply H₃. apply subset. assumption.
                        +++++ apply deduction.
                            ++++++ intros A J. apply H₁. apply K4_K. apply K_P. assumption.
                            ++++++ apply union. rewrite <- H. assumption.
                +++ apply Mp with [! [i]x !].
                    ++++ apply Ax with (axK4 i x).
                        +++++ apply H₁. apply K4_axK4.
                        +++++ reflexivity.
                    ++++ apply Prem. rewrite <- H. apply H₃. left. reflexivity.
    Qed.

    Fixpoint square (α : Sentence) (i : modal_index) : formula :=
    match α with
        | Contradiction   => [! #1 /\ ~#1 !]
        | Proposition a   => [! [i] #a !]
        | Conjunction ϕ ψ => [! square ϕ i /\ square ψ i !]
        | Disjunction ϕ ψ => [! square ϕ i \/ square ψ i !]
        | Implication ϕ ψ => [! [i] (square ϕ i -> square ψ i) !]
    end. 

    Fixpoint circle (α : Sentence) (i : modal_index) : formula :=
    match α with
        | Contradiction   => [! #1 /\ ~#1 !]
        | Proposition a   => [! #a !]
        | Conjunction ϕ ψ => [! circle ϕ i /\ circle ψ i !]
        | Disjunction ϕ ψ => [! [i] (circle ϕ i) \/ [i] (circle ψ i) !]
        | Implication ϕ ψ => [! [i] (circle ϕ i) -> circle ψ i !]
    end.

    Lemma splitting : forall M Γ α β, Subset P M -> (M; Γ |-- [! α !]) /\ (M; Γ |-- [! β !]) <-> (M; Γ |-- [! α /\ β !]).
    Proof.
        intros M Γ α β H₁. split. 
        + intros H₂. destruct H₂ as [H₃ H₄]. apply Mp with [! β !]. apply Mp with [! α !].
            ++ apply Ax with (ax4 α β).
                +++ apply H₁. apply P_ax4.
                +++ reflexivity.
            ++ assumption.
            ++ assumption.
        + intros H₂. split; apply Mp with [! α /\ β !].
            ++ apply Ax with (ax5 α β).
                +++ apply H₁. apply P_ax5.
                +++ reflexivity.
            ++ assumption.
            ++ apply Ax with (ax6 α β).
                +++ apply H₁. apply P_ax6.
                +++ reflexivity.
            ++ assumption.
    Qed.

    Lemma nec_and_distribution : forall M α β i, Subset (T i) M -> (M; ∅ |-- [! [i]α /\ [i]β !]) -> M; ∅ |-- [! [i](α /\ β) !].
    Proof.
        intros M α β i H₁ H₂.
        apply Nec. apply Mp with β. apply Mp with α.
        + apply Ax with (ax4 α β).
            ++ apply H₁. apply T_K. apply K_P. apply P_ax4.
            ++ reflexivity.
        + apply splitting in H₂.
            ++ destruct H₂ as [H₂ _]. apply Mp with [! [i]α !].
                +++ apply Ax with (axT i α). apply H₁. apply T_axT. reflexivity.
                +++ assumption.
            ++ intros A H₃. apply H₁. apply T_K. apply K_P. assumption.
        + apply splitting in H₂.
            ++ destruct H₂ as [_ H₂]. apply Mp with [! [i]β !].
                +++ apply Ax with (axT i β). apply H₁. apply T_axT. reflexivity.
                +++ assumption.
            ++ intros A H₃. apply H₁. apply T_K. apply K_P. assumption.
    Qed.

    Theorem equivalence : forall (α : Sentence) i, (S4 i ; Empty |-- Box i (circle α i)) <-> (S4 i ; Empty |--  square α i).
    Proof.
    intros.
    split.
    + intros. induction α as [ | a | α H₁ β H₂ | α H₁ β H₂ | α H₁ β H₂].
        ++ apply Mp with (Box i (circle ⊥ i)).
            +++ apply Ax with (axT i (square ⊥ i)).
                * apply S4_T. apply T_axT.
                * reflexivity.
            +++ assumption.
        ++ assumption.
        ++ apply Mp with (square β i).
            +++ apply Mp with (square α i).
                * apply Ax with (ax4 (square α i) (square β i)).
                    ** apply S4_T, T_K, K_P, P_ax4.
                    ** reflexivity.
                * apply H₁. apply Nec. apply Mp with (circle (α ∧ β) i).
                    ** apply Ax with (ax5 (circle α i) (circle β i)).
                        *** apply S4_T, T_K, K_P, P_ax5.
                        *** reflexivity.
                    ** apply Mp with (Box i (circle (α ∧ β) i)).
                        *** apply Ax with (axT i (circle (α ∧ β) i)).
                            - apply S4_T, T_axT.
                            - reflexivity.
                        *** assumption.
            +++ apply H₂. apply Nec. apply Mp with (circle (α ∧ β) i).
                * apply Ax with (ax6 (circle α i) (circle β i)).
                    ** apply S4_T, T_K, K_P, P_ax6.
                    ** reflexivity.
                * apply Mp with (Box i (circle (α ∧ β) i)).
                    ** apply Ax with (axT i (circle (α ∧ β) i)).
                        *** apply S4_T, T_axT.
                        *** reflexivity.
                    ** assumption.
        ++ admit.
        ++ admit.
    + intros. induction α as [ | a | α H₁ β H₂ | α H₁ β H₂ | α H₁ β H₂].
        ++ apply Nec. assumption.
        ++ assumption.
        ++ apply nec_and_distribution.
            +++ intros A H₃. apply S4_T. assumption.
            +++ apply splitting.
                * intros A H₃. apply S4_T, T_K, K_P. assumption.
                * split.
                    ** apply H₁. apply splitting in H. destruct H as [H _]. assumption. intros A H1. apply S4_T, T_K, K_P. assumption.
                    ** apply H₂. apply splitting in H. destruct H as [_ H]. assumption. intros A H1. apply S4_T, T_K, K_P. assumption.
        ++ admit.
        ++ admit.
    Admitted.

    Lemma square_nec : forall Γ α i, S4 i ; Γ |-- Implies ( square α i) (Box i (square α i)).
    Proof.
        intros.
    Admitted.

    Lemma transitivity : forall M Γ α β γ, Subset P M -> M ; Γ |-- [! (α -> β) -> (β -> γ) -> α -> γ !].
    Proof.
        intros. apply deduction, deduction, deduction.
        + assumption.
        + assumption.
        + assumption.
        + apply Mp with β.
            ++ apply Prem. left. right. reflexivity.
            ++ apply Mp with α.
                +++ apply Prem. left. left. right. reflexivity.
                +++ apply Prem. right. reflexivity.
    Qed.

    Inductive Squared (Γ : Theory) (i : modal_index): theory :=
    | Squaring : forall α, Γ α -> Squared Γ i (square α i).

    Theorem correctness : forall Γ α i, (Γ ⊢ α) -> S4 i; Squared Γ i |-- square α i.
    Proof.
        intros. induction H as [Γ α H | | | | | | | | | | Γ α β H₁ H₃ H₂ H₄].
        + apply Prem. apply Squaring. assumption.
        + apply Nec. apply Mp with (Implies (Box i (square α i)) (Box i (Implies (square β i) (square α i)))).
            ++ apply Mp with (Implies (square α i) (Box i (square α i))).
                +++ apply transitivity. intros A H. apply S4_T, T_K, K_P. assumption.
                +++ apply square_nec.
            ++ apply Mp with (Box i (Implies (square α i) (Implies (square β i) (square α i)))).
                +++ apply Ax with (axK i (square α i) (Implies (square β i) (square α i))).
                    * apply S4_T, T_K, K_axK.
                    * reflexivity.
                +++ apply Nec. apply Ax with (ax1 (square α i) (square β i)).
                * apply S4_T, T_K, K_P, P_ax1.
                * reflexivity.
        + admit.
        + admit.
        + apply Nec. apply Ax with (ax5 (square α i) (square β i)).
            ++ apply S4_T, T_K, K_P, P_ax5.
            ++ reflexivity.
        + apply Nec. apply Ax with (ax6 (square α i) (square β i)).
            ++ apply S4_T, T_K, K_P, P_ax6.
            ++ reflexivity.
        + apply Nec. apply Ax with (ax7 (square α i) (square β i)).
            ++ apply S4_T, T_K, K_P, P_ax7.
            ++ reflexivity.
        + apply Nec. apply Ax with (ax8 (square α i) (square β i)).
            ++ apply S4_T, T_K, K_P, P_ax8.
            ++ reflexivity.
        + admit.
        + apply Nec. apply deduction.
            ++ intros A H. apply S4_T, T_K, K_P. assumption.
            ++ apply consistency_deduction.
                +++ intros A H. apply S4_T, T_K, K_P. assumption.
                +++ unfold Consistent. intros H. specialize H with [! #1 !]. apply H,  Prem. right. right. reflexivity.
        + apply Mp with (square α i).
            ++ apply Mp with (square (α → β) i).
                +++ apply Ax with (axT i (Implies (square α i)  (square β i))).
                    * apply S4_T, T_axT.
                    * reflexivity.
                +++ assumption.
            ++ assumption.
    Admitted.
End Translations.