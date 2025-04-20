Require Import Modal_Library Modal_Notations Modal_Tactics Deductive_System Sets Completeness List.
Set Implicit Arguments.

Section Translations.
    Context `{X : modal_index_set}.

    Inductive Sentence : Set :=
    | Contradiction : Sentence
    | Proposition   : nat -> Sentence
    | Conjunction   : Sentence -> Sentence -> Sentence
    | Disjunction   : Sentence -> Sentence -> Sentence
    | Implication   : Sentence -> Sentence -> Sentence.

    Notation " ⊥ "     := Contradiction.
    Notation " # a "   := (Proposition a)   (at level 2, no associativity, a constr at level 1, format "# a").
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

    Inductive Deduction : Theory -> Sentence -> Prop :=
    | R₁ : forall Γ α,     Γ α -> Deduction Γ α
    | A₁ : forall Γ α β,   Deduction Γ (α → β → α)
    | A₂ : forall Γ α β γ, Deduction Γ ((α → β → γ) → (α → β) → α → γ)
    | A₃ : forall Γ α β,   Deduction Γ (α → β → α ∧ β)
    | A₄ : forall Γ α β,   Deduction Γ (α ∧ β → α)
    | A₅ : forall Γ α β,   Deduction Γ (α ∧ β → β)
    | A₆ : forall Γ α β,   Deduction Γ (α → α ∨ β)
    | A₇ : forall Γ α β,   Deduction Γ (β → α ∨ β)
    | A₈ : forall Γ α β γ, Deduction Γ ((α → γ) → (β → γ) → α ∨ β → γ )
    | A₉ : forall Γ α,     Deduction Γ (⊥ → α)
    | R₃ : forall Γ α β,   Deduction Γ (α → β) -> Deduction Γ α ->  Deduction Γ β.

    Notation "Γ ⊢ α" := (Deduction Γ α) (at level 110, no associativity).

    Notation " ∅ " := Empty.
    Notation " A ∪ B " := (Union A B) (at level 48, left associativity).
    Notation " [ a ] " := (Singleton a) (at level 0, right associativity).

    Inductive Boxed Γ i : formula -> Prop :=
    | Boxing : forall α, Γ α -> Boxed Γ i [! [i]α !].

    Lemma unboxing : forall Γ α i, (Boxed Γ i) α -> exists φ, α = [! [i]φ !].
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

    Theorem union : forall M Δ α β, (M; (Fin (β :: Δ)) |-- α) -> (M; [β] ∪ Fin Δ |-- α).
    Proof.
        intros. inversion H.
        + destruct H0.
            ++ rewrite H0. apply Prem. left. reflexivity.
            ++ apply Prem. right. assumption.
        + apply Ax with a.
            ++ assumption.
            ++ assumption.
        + apply Mp with f.
            ++ admit.
            ++ admit.
        + apply Nec. assumption.
    Admitted.

    Theorem nec_gen : forall Γ (α : formula) i, (S4 i; Boxed Γ i |-- [! α !]) -> S4 i; Boxed Γ i |-- [! [i]α !].
    Proof.
        intros Γ α i H₁.
        apply finite_world in H₁.
        destruct H₁ as [Δ H₁ H₂].
        generalize dependent α.
        induction Δ as [ | β Δ H₄].
        + intros. apply Nec. apply derive_weak with (Boxed (Fin []) i).
            ++ intros β H2. apply Boxed_fin_empty_is_empty with i. assumption.
            ++ apply derive_weak with (Fin []).
                +++ intros a B. apply fin_empty_is_empty in B. contradiction.
                +++ assumption.
        + intros α H₅. assert (Boxed Γ i β).
            ++ apply H₂. left. reflexivity.
            ++ apply unboxing in H. destruct H. apply Mp with [! [i][i]x !].
                +++ apply Mp with [! [i]([i]x -> α) !].
                    ++++ apply Ax with (axK i [! [i]x !] α).
                        +++++ apply S4_T, T_K. apply K_axK.
                        +++++ reflexivity.
                    ++++ apply H₄.
                        +++++ intros γ J. apply H₂. apply subset. assumption.
                        +++++ apply modal_deduction.
                            ++++++ repeat constructor. assumption.
                            ++++++ apply union. rewrite <- H. assumption.
                +++ apply Mp with [! [i]x !].
                    ++++ apply Ax with (axK4 i x).
                        +++++ apply S4_axK4.
                        +++++ reflexivity.
                    ++++ apply Prem. rewrite <- H. apply H₂. left. reflexivity.
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

    Lemma unnecessity : forall M Γ α i, Subset (T i) M -> (M ; Γ |-- [! [i]α!]) -> M ; Γ |-- α.
    Proof.
        intros M Γ α i H₁ H₂. apply Mp with [! [i]α!].
        + apply Ax with (axT i α).
            ++ apply H₁. apply T_axT.
            ++ reflexivity.
        + assumption.
    Qed.

    Lemma or_intro_left : forall M Γ α β γ, Subset P M -> M ; Γ |-- [! (α -> β) -> α -> β \/ γ !].
    Proof.
        intros. repeat (apply modal_deduction); try assumption.
        apply Mp with β.
        + apply Ax with (ax7 β γ).
            ++ apply H, P_ax7.
            ++ reflexivity.
        + apply Mp with α.
            ++ apply Prem. right. left. reflexivity.
            ++ apply Prem. left. reflexivity.
    Qed.

    Lemma or_intro_right : forall M Γ α β γ, Subset P M -> M ; Γ |-- [! (α -> β) -> α -> γ \/ β !].
    Proof.
        intros. repeat (apply modal_deduction); try assumption.
        apply Mp with β.
        + apply Ax with (ax8 γ β).
            ++ apply H, P_ax8.
            ++ reflexivity.
        + apply Mp with α.
            ++ apply Prem. right. left. reflexivity.
            ++ apply Prem. left. reflexivity.
    Qed.

    Lemma or_exchange : forall M Γ α β γ δ, Subset P M -> M ; Γ |-- [! (α -> γ) -> (β -> δ) -> α \/ β -> γ \/ δ !].
    Proof.
        intros. repeat (apply modal_deduction); try assumption.
        apply Mp with [! α \/ β !].
        + apply Mp with [! β -> γ \/ δ !].
            ++ apply Mp with [! α -> γ \/ δ !].
                +++ apply Ax with (ax9 α β [! γ \/ δ !]).
                    * apply H, P_ax9.
                    * reflexivity.
                +++ apply Mp with [! α -> γ !].
                    * apply or_intro_left. assumption.
                    * apply Prem. right. right. left. reflexivity.
            ++ apply Mp with [! β -> δ !].
                +++ apply or_intro_right. assumption.
                +++ apply Prem. right. left. reflexivity.
        + apply Prem. left. reflexivity.
    Qed.

    Theorem equivalence : forall (α : Sentence) i, (S4 i ; Empty |-- Box i (circle α i)) <-> (S4 i ; Empty |--  square α i).
    Proof.
    intros. split.
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
        ++ apply Mp with (circle (α ∨ β) i).
            +++ apply Mp with (Implies (circle β i) (square β i)).
                * admit.
                * apply modal_deduction.
                    ** admit.
                    ** admit.
            +++ admit.
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

    Lemma square_nec : forall Γ α i, S4 i ; Γ |-- Implies (square α i) (Box i (square α i)).
    Proof.
        intros.
        induction α as [ | | α H₁ β H₂ | | ].
        + admit.
        + apply Ax with (axK4 i [! #n !]).
            ++ apply S4_axK4.
            ++ reflexivity.
        + apply modal_deduction.
            ++ repeat constructor. assumption.
            ++ apply Mp with (And (Box i (square α i)) (Box i (square β i))).
                +++ admit.
                +++ apply Mp with (Box i (square β i)).
                    * admit.
                    * apply Mp with (square β i).
                        ** apply derive_weak with Γ.
                            *** right. assumption.
                            *** assumption.
                        ** apply Mp with (square (α ∧ β) i).
                            *** apply Ax with (ax6 (square α i) (square β i)).
                                - repeat constructor.
                                - reflexivity.
                            *** apply Prem. left. reflexivity.
        + admit.
        + apply Ax with (axK4 i (Implies (square α1 i) (square α2 i))).
            ++ apply S4_axK4.
            ++ reflexivity.
    Admitted.

    Lemma transitivity : forall M Γ α β γ, Subset P M -> M ; Γ |-- [! (α -> β) -> (β -> γ) -> α -> γ !].
    Proof.
        intros. repeat (apply modal_deduction).
        + assumption.
        + assumption.
        + assumption.
        + apply Mp with β.
            ++ apply Prem. right. left. reflexivity.
            ++ apply Mp with α.
                +++ apply Prem. right. right. left. reflexivity.
                +++ apply Prem. left. reflexivity.
    Qed.

    Lemma strict_deduction : forall Γ α β i, (S4 i ; [α] ∪ (Boxed Γ i) |-- β) -> S4 i ; (Boxed Γ i) |-- [! [i](α -> β) !].
    Proof.
        intros Γ α β i H₁.
        apply nec_gen.
        apply modal_deduction.
        + repeat constructor. assumption.
        + assumption.
    Qed.

    Lemma context_box : forall M α β i, (M ; (Boxed ([α] ∪ ∅) i) |-- β) -> M ; [[! [i]α !]] ∪ ∅ |-- β.
    Proof.
        intros. admit.
    Admitted.

    Inductive Squared (Γ : Theory) (i : modal_index): theory :=
    | Squaring : forall α, Γ α -> Squared Γ i (square α i).

    Theorem boxing : forall M Δ α β i, (M;  (Boxed ([α] ∪ Δ) i) |-- β) -> M; ([[! [i]α!]] ∪ (Boxed Δ i)) |-- β.
    Proof.
        intros.
        inversion H.
        + apply Prem. assert (Subset ((Boxed ([α] ∪ Δ) i)) (([[! [i]α!]] ∪ (Boxed Δ i)))).
            ++ intros a J. admit.
            ++ apply H3. assumption.
        + apply Ax with a.
            ++ assumption.
            ++ assumption.
        + admit.
        + admit.
    Admitted.

    Theorem strict_ponens : forall Γ α β i, (S4 i; Γ |-- [! [i](α -> β) !]) -> (S4 i; Γ |-- α) -> S4 i; Γ |-- β.
    Proof.
        intros Γ α β i H₁ H₂.
        apply Mp with α.
        + apply Mp with [! [i](α -> β) !].
            ++ apply Ax with (axT i [! α -> β !]).
                +++ apply S4_T, T_axT.
                +++ reflexivity.
            ++ assumption.
        + assumption.
    Qed.

    Theorem soundness : forall Γ α i, (Γ ⊢ α) -> S4 i; Squared Γ i |-- square α i.
    Proof.
        intros. induction H as [Γ α H | | | | | | | | | | Γ α β H₁ H₃ H₂ H₄].
        + apply Prem. apply Squaring. assumption.
        + apply Nec. apply Mp with (Implies (Box i (square α i)) (Box i (Implies (square β i) (square α i)))).
            ++ apply Mp with (Implies (square α i) (Box i (square α i))).
                +++ apply transitivity. repeat constructor. assumption.
                +++ apply square_nec.
            ++ apply Mp with (Box i (Implies (square α i) (Implies (square β i) (square α i)))).
                +++ apply Ax with (axK i (square α i) (Implies (square β i) (square α i))).
                    * apply S4_T, T_K, K_axK.
                    * reflexivity.
                +++ apply Nec. apply Ax with (ax1 (square α i) (square β i)).
                * repeat constructor.
                * reflexivity.
        + apply Nec. apply modal_deduction.
            ++ repeat constructor. assumption.
            ++ fold square. apply context_box. apply strict_deduction. apply boxing. apply strict_deduction.
                +++ apply strict_ponens with (square β i).
                    * apply strict_ponens with (square α i).
                        ** apply Prem. right. apply Boxing. right. left. reflexivity.
                        ** apply Prem. left. reflexivity.
                    * apply strict_ponens with (square α i).
                        ** apply Prem. right. apply Boxing. left. reflexivity.
                        ** apply Prem. left. reflexivity.
        + apply Nec. apply Mp with (Implies (Box i (square α i)) (Box i (Implies (square β i) (And (square α i) (square β i))))).
            ++ apply Mp with (Implies (square α i) (Box i (square α i))).
                +++ apply transitivity. repeat constructor. assumption.
                +++ apply square_nec.
            ++ apply Mp with (Box i (Implies (square α i) (Implies (square β i) (And (square α i) (square β i))))).
                +++ apply Ax with (axK i (square α i) (Implies (square β i) (And (square α i) (square β i)))).
                    * apply S4_T, T_K, K_axK.
                    * reflexivity.
                +++ apply Nec. apply Ax with (ax4 (square α i) (square β i)).
                    * repeat constructor.
                    * reflexivity.
        + apply Nec. apply Ax with (ax5 (square α i) (square β i)). repeat constructor. reflexivity.
        + apply Nec. apply Ax with (ax6 (square α i) (square β i)). repeat constructor. reflexivity.
        + apply Nec. apply Ax with (ax7 (square α i) (square β i)). repeat constructor. reflexivity.
        + apply Nec. apply Ax with (ax8 (square α i) (square β i)). repeat constructor. reflexivity.
        + apply Nec. apply modal_deduction.
            ++ repeat constructor. assumption.
            ++ fold square. apply context_box.
               apply strict_deduction, boxing.
               apply strict_deduction.
               apply Mp with (Or (square α i) (square β i)).
                   +++ apply Mp with (Implies (square β i) (square γ i)).
                       * apply Mp with (Implies (square α i) ((square γ i))).
                           ** apply Ax with (ax9 (square α i) (square β i) (square γ i)).
                               *** repeat constructor.
                               *** reflexivity.
                           ** apply Mp with (Box i (Implies (square α i) (square γ i))).
                               *** apply Ax with (axT i (Implies (square α i) (square γ i))).
                                   - apply S4_T, T_axT.
                                   - reflexivity.
                               *** apply Prem. right. apply Boxing. right. left. reflexivity.
                       * apply Mp with (Box i (Implies (square β i) (square γ i))).
                           ** apply Ax with (axT i (Implies (square β i) (square γ i))).
                               *** apply S4_T, T_axT.
                               *** reflexivity.
                           ** apply Prem. right. apply Boxing. left. reflexivity.
                   +++ apply Prem. left. reflexivity. 
        + apply Nec. apply modal_deduction.
            ++ repeat constructor. assumption.
            ++ apply consistency_deduction.
                +++ intros A H. apply S4_T, T_K, K_P. assumption.
                +++ unfold Consistent. intros H. specialize H with [! #1 !]. apply H, Prem. right. left. reflexivity.
        + apply Mp with (square α i).
            ++ apply Mp with (square (α → β) i).
                +++ apply Ax with (axT i (Implies (square α i)  (square β i))).
                    * apply S4_T, T_axT.
                    * reflexivity.
                +++ assumption.
            ++ assumption.
    Qed.
End Translations.