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

    Theorem importation : forall A Γ α β γ, Subset P A -> (A ; Γ |-- [! α -> β -> γ !]) -> A ; Γ |-- [! α /\ β -> γ !].
    Proof.
        intros A Γ α β γ H₁ H₂.
        apply modal_deduction.
        assumption.
        apply Mp with β.
        apply Mp with α.
        + apply derive_weak with Γ.
          * right.
            assumption.
          * assumption.
        + apply modal_ax5 with β.
          * apply H₁.
            repeat constructor.
          * apply Prem.
            left.
            reflexivity.
        + apply modal_ax6 with α.
          * apply H₁.
            repeat constructor.
          * apply Prem.
            left.
            reflexivity.
    Qed.

    Definition Boxed (Γ : theory) i := forall α, Γ α -> exists β, α = [! [i]β !].

    Theorem nec_gen : forall Γ α i, Boxed Γ i -> (S4 i; Γ |-- [! α !]) -> S4 i; Γ |-- [! [i]α !].
    Proof.
        intros Γ φ i H₁ H₂.
        apply finite_world in H₂.
        destruct H₂ as [Δ H₂ H₃].
        generalize dependent φ.
        induction Δ as [ | φ Δ H₄].
        + intros.
          apply Nec.
          apply derive_weak with (Fin []).
          intros α H₄.
          contradiction.
          assumption.
        + intros β H₅.
          assert (Γ φ) as H₆.
          apply H₃.
          left.
          reflexivity.
          apply H₁ in H₆.
          destruct H₆ as [α H₆].
          apply Mp with [! [i]α !].
          * apply modal_syllogism with [! [i][i]α !].
            - repeat constructor.
            - repeat constructor.
            - apply modal_axK4, S4_axK4.
            - apply modal_axK.
              constructor.
              constructor.
              apply K_axK.
              apply H₄.
              intros γ H₇.
              apply H₃.
              right.
              assumption.
              apply modal_deduction.
              repeat constructor.
              assumption.
              rewrite <- H₆.
              apply union.
              assumption.
          * apply Prem.
            apply H₃.
            left.
            assumption.
    Qed.

    Lemma modal_axT : forall A Γ α i, Subset (T i) A -> (A ; Γ |-- [! [i]α !]) -> A ; Γ |-- α.
    Proof.
      intros A Γ α i H₁ H₂.
      apply Mp with [! [i]α !].
      + apply Ax with (axT i α).
        * apply H₁.
          apply T_axT.
        * reflexivity.
      + assumption.
    Qed.

    Lemma nec_and_distribution : forall Γ α β i, S4 i; Γ |-- [! [i](α /\ β) -> [i]α /\ [i]β !].
    Proof.
      intros Γ α β i.
      apply derive_weak with ∅.
      intros γ H.
      contradiction.
      apply modal_deduction.
      repeat constructor.
      assumption.
      apply modal_ax4.
      + repeat constructor.
      + repeat constructor.
      + repeat constructor.
      + apply nec_gen.
        * intros γ H₁.
          exists [! α /\ β !].
          inversion H₁ as [H₂ | H₂].
          inversion H₂.
          reflexivity.
          contradiction.
        * apply modal_ax5 with β.
          repeat constructor.
          apply modal_axT with i.
          constructor.
          assumption.
          apply Prem.
          left.
          reflexivity.
      + apply nec_gen.
        * intros γ H₁.
          exists [! α /\ β !].
          inversion H₁ as [H₂ | H₂].
          inversion H₂.
          reflexivity.
          contradiction.
        * apply modal_ax6 with α.
          repeat constructor.
          apply modal_axT with i.
          constructor.
          assumption.
          apply Prem.
          left.
          reflexivity.
    Qed.

    Lemma nec_and_undistribution : forall Γ α β i, S4 i; Γ |-- [! [i]α /\ [i]β -> [i](α /\ β) !].
    Proof.
      intros Γ α β i.
      apply derive_weak with ∅.
      intros γ H.
      contradiction.
      apply importation.
      repeat constructor.
      assumption.
      apply modal_deduction, modal_deduction.
      repeat constructor.
      assumption.
      repeat constructor.
      assumption.
      apply nec_gen.
      + intros γ H₁.
        inversion H₁ as [H₂ | [H₂ | H₂]].
        * exists β.
          inversion H₂.
          reflexivity.
        * exists α.
          inversion H₂.
          reflexivity.
        * contradiction.
      + apply modal_ax4.
        * repeat constructor.
        * repeat constructor.
        * repeat constructor.
        * apply modal_axT with i.
          constructor.
          assumption.
          apply Prem.
          right.
          left.
          reflexivity.
        * apply modal_axT with i.
          constructor.
          assumption.
          apply Prem.
          left.
          reflexivity.
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

    Notation "α ? i" := (square α i) (in custom modal at level 90).
    Notation "α ! i" := (circle α i) (in custom modal at level 90).

    Lemma splitting : forall M Γ α β, Subset P M -> (M; Γ |-- [! α !]) /\ (M; Γ |-- [! β !]) <-> (M; Γ |-- [! α /\ β !]).
    Proof.
        intros M Γ α β H₁. split.
        + intros H₂. destruct H₂ as [H₃ H₄]. apply Mp with [! β !]. apply Mp with [! α !].
            ++ apply Ax with (ax4 α β).
                +++ apply H₁. constructor.
                +++ reflexivity.
            ++ assumption.
            ++ assumption.
        + intros H₂. split; apply Mp with [! α /\ β !].
            ++ apply Ax with (ax5 α β).
                +++ apply H₁. constructor.
                +++ reflexivity.
            ++ assumption.
            ++ apply Ax with (ax6 α β).
                +++ apply H₁. constructor.
                +++ reflexivity.
            ++ assumption.
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

    Lemma or_exchange : forall M Γ α β γ δ, Subset P M -> (M ; Γ |-- [! α -> γ !]) -> (M ; Γ |-- [! β -> δ !]) -> (M ; Γ |-- [! α \/ β -> γ \/ δ !]).
    Proof.
      intros M Γ α β γ δ H₁ H₂ H₃.
      apply modal_deduction.
      assumption.
      apply modal_ax9 with α β.
      apply H₁.
      constructor.
      * apply Mp with [! α -> γ !].
        + apply or_intro_left.
          assumption.
        + apply derive_weak with Γ.
          right.
          assumption.
          assumption.
      * apply Mp with [! β -> δ !].
        + apply or_intro_right.
          assumption.
        + apply derive_weak with Γ.
          right.
          assumption.
          assumption.
      * apply Prem.
        left.
        reflexivity.
    Qed.

    Lemma nec_or_distribution : forall Γ α β i, (S4 i; Γ |-- [! [i]α \/ [i]β -> [i](α \/ β) !]).
    Proof.
        intros Γ α β i.
        apply derive_weak with Empty.
        intros γ H.
        contradiction.
        apply Mp with [! [i]β -> [i](α \/ β) !].
        apply Mp with [! [i]α -> [i](α \/ β) !].
        + apply Ax with (ax9 [! [i]α !] [! [i]β !] [! [i](α \/ β) !]).
          repeat constructor.
          reflexivity.
        + apply modal_deduction.
          repeat constructor.
          assumption.
          apply nec_gen.
          intros γ H.
          destruct H.
          * destruct H.
            exists α.
            reflexivity.
          * destruct H.
          * apply modal_ax7.
            repeat constructor.
            apply modal_axT with i.
            constructor.
            assumption.
            apply Prem.
            left.
            reflexivity.
        + apply modal_deduction.
          repeat constructor.
          assumption.
          apply nec_gen.
          intros γ H.
          destruct H.
          * destruct H.
            exists β.
            reflexivity.
          * destruct H.
          * apply modal_ax8.
            repeat constructor.
            apply modal_axT with i.
            constructor.
            assumption.
            apply Prem.
            left.
            reflexivity.
    Qed.

    Inductive Imboxed Γ i : formula -> Prop :=
    | Imboxing : forall α, Γ α -> Imboxed Γ i [! [i]α !].

    Inductive Squared Γ i : formula -> Prop :=
    | Squaring : forall α, Γ α -> Squared Γ i [! α ? i !].

    Inductive Circled Γ i : formula -> Prop :=
    | Circling : forall α, Γ α -> Circled Γ i [! α ! i !].

    Lemma strict_deduction : forall Γ α β i, Boxed Γ i -> (S4 i ; [α] ∪ Γ |-- β) -> S4 i ; Γ |-- [! [i](α -> β) !].
    Proof.
      intros Γ α β i H₁ H₂.
      apply nec_gen.
      + assumption.
      + apply modal_deduction.
        * repeat constructor. assumption.
        * assumption.
    Qed.

    Theorem strict_ponens : forall Γ α β i, (S4 i; Γ |-- [! [i](α -> β) !]) -> (S4 i; Γ |-- α) -> S4 i; Γ |-- β.
    Proof.
      intros Γ α β i H₁ H₂.
      apply Mp with α.
      + apply Mp with [! [i](α -> β) !].
        * apply Ax with (axT i [! α -> β !]).
          - apply S4_T, T_axT.
          - reflexivity.
        * assumption.
      + assumption.
    Qed.

    Theorem equivalence : forall Γ (α : Sentence) i, S4 i ; Γ |-- [! [i](α ! i) <-> (α ? i) !].
    Proof.
      intros Γ α i.
      apply derive_weak with ∅.
      intros β H.
      contradiction.
      induction α as [ | | α H₁ β H₂ | α H₁ β H₂ | α H₁ β H₂].
      + apply splitting.
        repeat constructor.
        assumption.
        split.
        * apply Ax with (axT i (square ⊥ i)).
          - apply S4_T, T_axT.
          - reflexivity.
        * apply modal_deduction.
          - repeat constructor.
            assumption.
          - apply consistency_deduction.
            repeat constructor.
            assumption.
            intros H.
            unfold Consistent in H.
            specialize H with [! #1 !].
            apply H.
            apply Prem.
            right.
            left.
            reflexivity.
        + apply splitting.
          repeat constructor.
          assumption.
          split.
          * apply derive_identity.
            repeat constructor.
            assumption.
          * apply derive_identity.
            repeat constructor.
            assumption.
        + apply splitting.
          repeat constructor.
          assumption.
          split.
          * apply modal_deduction.
            repeat constructor.
            assumption.
            apply modal_ax4.
            - repeat constructor.
            - repeat constructor.
            - repeat constructor.
            - fold square.
              apply Mp with [! [i](α ! i) !].
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax5 with [! (α ? i) -> [i](α ! i) !].
              repeat constructor.
              assumption.
              apply modal_ax5 with [! [i](β ! i) !].
              repeat constructor.
              apply Mp with [! [i]((α ! i) /\ (β ! i)) !].
              apply nec_and_distribution.
              apply Prem.
              left.
              reflexivity.
            - fold square.
              apply Mp with [! [i](β ! i) !].
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax5 with [! (β ? i) -> [i](β ! i) !].
              repeat constructor.
              assumption.
              apply modal_ax6 with [! [i](α ! i) !].
              repeat constructor.
              apply Mp with [! [i]((α ! i) /\ (β ! i)) !].
              apply nec_and_distribution.
              apply Prem.
              left.
              reflexivity.
          * apply modal_deduction.
            repeat constructor.
            assumption.
            apply Mp with [! [i](α ! i) /\ [i](β ! i) !].
            apply nec_and_undistribution.
            apply modal_ax4.
            - repeat constructor.
            - repeat constructor.
            - repeat constructor.
            - apply Mp with [! α ? i !].
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax6 with [! [i](α ! i) -> (α ? i) !].
              repeat constructor.
              assumption.
              apply modal_ax5 with [! β ? i !].
              repeat constructor.
              apply Prem.
              left.
              reflexivity.
            - apply Mp with [! β ? i !].
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax6 with [! [i](β ! i) -> (β ? i) !].
              repeat constructor.
              assumption.
              apply modal_ax6 with [! α ? i !].
              repeat constructor.
              apply Prem.
              left.
              reflexivity.
        + apply splitting.
          repeat constructor.
          assumption.
          split.
          * apply modal_deduction.
            repeat constructor.
            assumption.
            apply Mp with [! [i](α ! i) \/ [i](β ! i) !].
            apply or_exchange.
            - repeat constructor.
              assumption.
            - fold square.
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax5 with [! (α ? i) -> [i](α ! i) !].
              repeat constructor.
              assumption.
            - fold square.
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax5 with [! (β ? i) -> [i](β ! i) !].
              repeat constructor.
              assumption.
            - apply modal_axT with i.
              constructor.
              assumption.
              apply Prem.
              left.
              reflexivity.
          * apply modal_deduction.
            repeat constructor.
            assumption.
            apply Mp with [! [i][i](α ! i) \/ [i][i](β ! i) !].
            apply nec_or_distribution.
            apply Mp with [! (α ? i) \/ (β ? i) !].
            apply or_exchange.
            - repeat constructor.
              assumption.
            - apply modal_syllogism with [! [i](α ! i) !].
              repeat constructor.
              repeat constructor.
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax6 with [! [i](α ! i) -> (α ? i) !].
              repeat constructor.
              assumption.
              apply Ax with (axK4 i [! α ! i!]).
              apply S4_axK4.
              reflexivity.
            - apply modal_syllogism with [! [i](β ! i) !].
              repeat constructor.
              repeat constructor.
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax6 with [! [i](β ! i) -> (β ? i) !].
              repeat constructor.
              assumption.
              apply Ax with (axK4 i [! β ! i!]).
              apply S4_axK4.
              reflexivity.
            - apply Prem.
              left.
              reflexivity.
        + apply splitting.
          repeat constructor.
          assumption.
          split.
          * apply modal_deduction.
            repeat constructor.
            assumption.
            apply strict_deduction.
            intros γ H₃.
            destruct H₃ as [H₃ | H₃].
            destruct H₃.
            exists (circle (α → β) i).
            reflexivity.
            contradiction.
            fold square.
            apply Mp with [! α ? i !].
            - apply modal_syllogism with [! [i](β ! i) !].
              repeat constructor.
              repeat constructor.
              apply modal_syllogism with [! [i](α ! i) !].
              repeat constructor.
              repeat constructor.
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax6 with [! [i](α ! i) -> (α ? i) !].
              repeat constructor.
              assumption.
              apply derive_weak with (Extend (Box i (circle (α → β) i)) ∅).
              right.
              assumption.
              apply modal_deduction.
              repeat constructor.
              assumption.
              apply nec_gen.
              intros γ H₃.
              destruct H₃ as [H₃ | [H₃ | H₃]].
              destruct H₃.
              exists [! (α ! i) !].
              reflexivity.
              destruct H₃.
              exists (circle (α → β) i).
              reflexivity.
              contradiction.
              apply Mp with  [! [i](α ! i) !].
              apply modal_axT with i.
              constructor.
              assumption.
              apply Prem.
              right.
              left.
              reflexivity.
              apply Prem.
              left.
              reflexivity.
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax5 with [! (β ? i) -> [i](β ! i) !].
              repeat constructor.
              assumption.
            - apply Prem.
              left.
              reflexivity.
          * apply modal_deduction.
            repeat constructor.
            assumption.
            apply strict_deduction.
            intros γ H₃.
            destruct H₃ as [H₃ | H₃].
            - destruct H₃.
              exists [! (α ? i) -> (β ? i) !].
              reflexivity.
            - contradiction.
            - fold circle.
              apply modal_axT with i.
              constructor.
              assumption.
              apply Mp with [! β ? i !].
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax6 with [! [i](β ! i) -> (β ? i)!].
              repeat constructor.
              assumption.
              apply Mp with [! [i](α ! i) !].
              apply modal_syllogism with [! (α ? i) !].
              repeat constructor.
              repeat constructor.
              apply derive_weak with ∅.
              left.
              contradiction.
              apply modal_ax5 with [! (α ? i) -> [i](α ! i) !].
              repeat constructor.
              assumption.
              apply modal_axT with i.
              constructor.
              assumption.
              apply Prem.
              right.
              left.
              reflexivity.
              apply Prem.
              left.
              reflexivity.
    Qed.

    Lemma square_nec : forall Γ α i, S4 i ; Γ |-- [! (α ? i) -> [i](α ? i) !].
    Proof.
        intros.
        induction α as [ | | α H₁ β H₂ | α H₁ β H₂ | α H₁ β H₂].
        + apply modal_deduction.
            * repeat constructor.
              assumption.
            * apply consistency_deduction.
              - repeat constructor.
                assumption.
              - intro.
                unfold Consistent in H.
                specialize H with [! #1 !].
                apply H.
                apply Prem.
                right.
                left.
                reflexivity.
        + apply modal_axK4.
          apply S4_axK4.
        + apply modal_deduction.
          * repeat constructor.
            assumption.
          * apply Mp with [! [i](α ? i) /\ [i](β ? i) !].
            - admit.
            - apply Mp with [! [i](β ? i) !].
              ++ admit.
              ++ apply Mp with [! β ? i !].
                 ** apply derive_weak with Γ.
                    -- right. 
                       assumption.
                    -- assumption.
                 ** apply Mp with (square (α ∧ β) i).
                    -- apply Ax with (ax6 [! α ? i !] [! β ? i !]).
                       repeat constructor.
                       reflexivity.
                    -- apply Prem.
                       left.
                       reflexivity.
        + apply modal_deduction.
          repeat constructor.
          assumption.
          apply Mp with [! [i](α ? i) \/ [i](β ? i) !].
          * admit.
          * apply Mp with [! (α ? i) \/ (β ? i) !].
            - apply or_exchange.
              repeat constructor.
              assumption.
              apply derive_weak with Γ.
              right.
              assumption.
              assumption.
              apply derive_weak with Γ.
              right.
              assumption.
              assumption.
            - apply Prem.
              left.
              reflexivity.
        + apply Ax with (axK4 i [! (α ? i) -> (β ? i) !]).
          * apply S4_axK4.
          * reflexivity.
    Admitted.

    Theorem el_nc_lf : forall Γ α β i, (S4 i ; Imboxed (Squared Γ i) i |-- [! [i]((α ? i) -> (β ? i)) !]) -> S4 i ; Squared Γ i |-- [! [i]((α ? i) -> (β ? i)) !].
    Proof.
      intros.
      remember (Imboxed (Squared Γ i) i) as Δ eqn : E₁.
      induction H as [Δ γ H₁ | Δ A γ H₁ H₂ | Δ γ δ _ H₁ _ H₂ | Δ γ j H₁ _].
      + rewrite E₁ in H₁.
        inversion H₁ as [δ H₂ H₃].
        inversion H₂ as [ɛ H₄ H₅].
        apply Mp with [! (ɛ ? i) !].
        apply square_nec.
        rewrite H₅.
        apply Prem.
        assumption.
      + apply Ax with A.
        assumption.
        assumption.
      + apply Mp with γ.
        apply H₁.
        assumption.
        apply H₂.
        assumption.
      + apply Nec.
        assumption.
    Qed.

    Theorem in_nc_rg : forall Γ α β i, (S4 i ; Squared Γ i |-- [! (α ? i) -> (β ? i) !]) -> S4 i ; Imboxed (Squared Γ i) i |-- [! (α ? i) -> (β ? i) !].
    Proof.
      intros.
      remember (Squared Γ i) as Δ eqn : E₁.
      induction H as [Δ γ H₁ | Δ A γ H₁ H₂ | Δ γ δ H₁ H₂ H₃ H₄ | Δ γ j H₁ H₂].
      + apply modal_axT with i.
        constructor.
        assumption.
        apply Prem.
        apply Imboxing.
        assumption.
      + apply Ax with A.
        assumption.
        assumption.
      + apply Mp with γ.
        apply H₂.
        assumption.
        apply H₄.
        assumption.
      + apply Nec.
        assumption.
    Qed.

    Lemma finite_world_v2 : forall M Γ α i, (M; Squared Γ i |-- α) -> exists2 Δ, (M; Squared (Fin Δ) i |-- α) & Subset (Squared (Fin Δ) i) (Squared Γ i).
    Proof.
      induction 1.
      + intros.
        exists ((square f i) :: nil).


    Theorem equivalencee : forall Γ α i, (S4 i ; Imboxed (Circled Γ i) i |-- [! (α ! i) !]) <-> (S4 i ; Squared Γ i |-- [! (α ? i) !]).
    Proof.
      intros Γ α i.
      split.
      * intros H.
        apply finite_world in H.
        destruct H as [Δ H₁ H₂].
        generalize dependent α.
        induction Δ as [ | φ Δ H₃].
        + intros α H₁.
          apply derive_weak with (Fin []).
          intros β H₃.
          contradiction.
          apply Mp with [! [i](α ! i) !].
          - apply modal_ax5 with [! (α ? i) -> [i](α ! i) !].
            repeat constructor.
            apply equivalence.
          - apply nec_gen.
            intros β H₃.
            contradiction.
            assumption.
        + intros α H₁.
          assert ((Imboxed (Circled Γ i) i) φ) as H₄.
          apply H₂.
          left.
          reflexivity.
          inversion H₄ as [β H₅ H₆].
          inversion H₅ as [γ H₇ H₈].
          apply Mp with [! (γ ? i) !].
          apply modal_axT with i.
          constructor.
          assumption.
          specialize H₃ with (γ → α).
          apply H₃.
          intros δ H₉.
          apply H₂.
          right.
          assumption.
          simpl.
          apply modal_deduction.
          repeat constructor.
          assumption.
          apply union.
          rewrite H₈.
          rewrite H₆.
          assumption.
          apply Prem.
          apply Squaring.
          assumption.
      * intros.
        apply finite_world in H.
        destruct H as [Δ H₁ H₂].
        generalize dependent α.
        induction Δ as [ | φ Δ H₃].
        + intros α H₁.
          apply derive_weak with (Fin []).
          intros β H₃.
          contradiction.
          apply modal_axT with i.
          constructor.
          assumption.
          apply Mp with [! (α ? i) !].
          - apply modal_ax6 with [! [i](α ! i) -> (α ? i) !].
            repeat constructor.
            apply equivalence.
          - assumption.
        + intros α H₁.
          assert ((Squared Γ i) φ) as H₄.
          apply H₂.
          left.
          reflexivity.
          destruct H₄ as [β H₄].
          apply Mp with [! [i](β ! i) !].
          specialize H₃ with (β → α).
          apply H₃.
          intros γ H₆.
          apply H₂.
          right.
          assumption.
          simpl.
          assert (exists Θ, forall φ, (S4 i; Squared Θ i |-- φ) <-> (S4 i; Fin Δ |-- φ)) as H₅.
          - 

    Theorem soundness : forall Γ α i, (Γ ⊢ α) -> S4 i; Squared Γ i |-- [! α ? i !].
    Proof.
        intros. induction H as [Γ α H | | | | | | | | | | Γ α β H₁ H₃ H₂ H₄].
        + apply Prem.
          apply Squaring.
          assumption.
        + apply Nec.
          fold square.
          apply modal_syllogism with [! [i](α ? i) !].
          * repeat constructor.
          * repeat constructor.
          * apply square_nec.
          * apply modal_axK.
            - constructor. constructor. apply K_axK.
            - apply Nec.
              apply Ax with (ax1 [! (α ? i) !] [! (β ? i) !]).
              repeat constructor.
              reflexivity.
        + apply Nec. fold square. apply modal_deduction.
          * repeat constructor.
            assumption.
          * repeat (apply strict_deduction).
            - intros φ H.
              destruct H.
              ++ inversion H.
                 exists [! (α ? i) -> [i]((β ? i) -> (γ ? i)) !].
                 reflexivity.
              ++ contradiction.
            - intros φ H.
              destruct H as [H | [H | H]].
              ++ inversion H.
                 exists [! (α ? i) -> (β ? i) !].
                 reflexivity.
              ++ inversion H.
                 exists [! (α ? i) -> [i]((β ? i) -> (γ ? i)) !].
                 reflexivity.
              ++ contradiction.
            - apply strict_ponens with (square β i).
              ++ apply strict_ponens with (square α i).
                 ** apply Prem.
                    right.
                    right.
                    left.
                    reflexivity.
                 ** apply Prem.
                    left.
                    reflexivity.
              ++ apply strict_ponens with [! α ? i !].
                 ** apply Prem.
                    right.
                    left.
                    reflexivity.
                 ** apply Prem.
                    left.
                    reflexivity.
        + apply Nec.
          fold square.
          apply modal_syllogism with [! [i](α ? i) !].
          * repeat constructor.
          * repeat constructor.
          * apply square_nec.
          * apply modal_axK.Fin Δ
            - constructor. constructor. apply K_axK.
            - apply Nec.
              apply Ax with (ax4 [! (α ? i) !] [! (β ? i) !]).
              repeat constructor.
              reflexivity.
        + apply Nec.
          apply Ax with (ax5 [! α ? i !] [! β ? i !]).
          repeat constructor.
          reflexivity.
        + apply Nec.
          apply Ax with (ax6 [! α ? i !] [! β ? i !]).
          repeat constructor.
          reflexivity.
        + apply Nec.
          apply Ax with (ax7 [! α ? i !] [! β ? i !]).
          repeat constructor.
          reflexivity.
        + apply Nec.
          apply Ax with (ax8 [! α ? i !] [! β ? i !]).
          repeat constructor.
          reflexivity.
        + apply Nec.
          fold square.
          apply modal_deduction.
          * repeat constructor.
            assumption.
          * repeat (apply strict_deduction).
            - intros φ H.
              destruct H as [H | H].
              inversion H.
              exists [! (α ? i) -> (γ ? i) !].
              reflexivity.
              contradiction.
            - intros φ H.
              destruct H as [H | H].
              inversion H.
              exists [! (β ? i) -> (γ ? i) !].
              reflexivity.
              destruct H as [H | H].
              inversion H.
              exists [! (α ? i) -> (γ ? i) !].
              reflexivity.
              contradiction.
            - apply modal_ax9 with [! (α ? i) !] [! (β ? i) !].
              ++ repeat constructor.
              ++ apply Mp with [! [i]((α ? i) -> (γ ? i)) !].
                 ** apply Ax with (axT i [! (α ? i) -> (γ ? i) !]).
                    -- constructor.
                       apply T_axT.
                    -- reflexivity.
                 ** apply Prem.
                    right.
                    right.
                    left.
                    reflexivity.
              ++ apply Mp with [! [i]((β ? i) -> (γ ? i)) !].
                 ** apply Ax with (axT i [! (β ? i) -> (γ ? i) !]).
                    -- constructor.
                       apply T_axT.
                    -- reflexivity.
                 ** apply Prem.
                    right.
                    left.
                    reflexivity.
              ++ apply Prem.
                 left.
                 reflexivity.
        + apply Nec.
          fold square.
          apply modal_deduction.
            ++ repeat constructor.
               assumption.
            ++ apply consistency_deduction.
                +++ repeat constructor.
                    assumption.
                +++ unfold Consistent.
                    intros H.
                    specialize H with [! #1 !].
                    apply H, Prem.
                    right.
                    left.
                    reflexivity.
        + apply Mp with [! α ? i !].
            ++ apply Mp with [! [i]((α ? i) -> (β ? i)) !].
                +++ apply Ax with (axT i [! (α ? i) -> (β ? i) !]).
                    * constructor. apply T_axT.
                    * reflexivity.
                +++ assumption.
            ++ assumption.
    Qed.
End Translations.