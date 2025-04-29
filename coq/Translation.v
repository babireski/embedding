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

    (* Inductive Boxed Γ i : formula -> Prop :=
    | Boxing : forall α, Γ α -> Boxed Γ i [! [i]α !]. *)

    Definition Boxed (Γ : theory) i := forall α, Γ α -> exists β, α = [! [i]β !].

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

    Theorem nec_gen : forall Γ α i, Boxed Γ i -> (S4 i; Γ |-- [! α !]) -> S4 i; Γ |-- [! [i]α !].
    Proof.
        intros Γ φ i H₁ H₂.
        apply finite_world in H₂.
        destruct H₂ as [Δ H₂ H₃].
        generalize dependent φ.
        induction Δ as [ | φ Δ H₄].
        + intros. apply Nec. apply derive_weak with (Fin []).
            ++ intros α H₄. contradiction.
            ++ assumption.
        + intros β H₅. assert (Γ φ) as H₆.
            ++ apply H₃. left. reflexivity.
            ++ apply H₁ in H₆. destruct H₆ as [α H₆]. apply Mp with [! [i]α !].
                +++ apply modal_syllogism with [! [i][i]α !].
                    * repeat constructor.
                    * repeat constructor.
                    * apply modal_axK4, S4_axK4.
                    * apply modal_axK.
                        ** constructor. constructor. apply K_axK.
                        ** apply H₄.
                            *** intros γ H₇. apply H₃. right. assumption.
                            *** apply modal_deduction.
                                - repeat constructor. assumption.
                                - rewrite <- H₆. apply union. assumption.
                +++ apply Prem. apply H₃. left. assumption.
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

    Lemma nec_and_distribution : forall Γ α β i, Boxed Γ i -> (S4 i; Γ |-- [! [i]α /\ [i]β !]) <-> (S4 i; Γ |-- [! [i](α /\ β) !]).
    Proof.
        intros Γ α β i H₁.
        split.
        + intros H₂. apply nec_gen. assumption. apply Mp with β. apply Mp with α.
            ++ apply Ax with (ax4 α β).
                +++ repeat constructor.
                +++ reflexivity.
            ++ apply splitting in H₂.
                +++ destruct H₂ as [H₂ _]. apply Mp with [! [i]α !].
                    * apply Ax with (axT i α). constructor. apply T_axT. reflexivity.
                    * assumption.
                +++ intros A H₃. repeat constructor. assumption.
            ++ apply splitting in H₂.
                +++ destruct H₂ as [_ H₂]. apply Mp with [! [i]β !].
                    * apply Ax with (axT i β). constructor. apply T_axT. reflexivity.
                    * assumption.
                +++ intros A H₃. repeat constructor. assumption.
        + intros H₂. apply Mp with [! [i]β !]. apply Mp with [! [i]α !].
            ++ apply Ax with (ax4 [! [i]α !] [! [i]β !]).
               repeat constructor.
               reflexivity.
            ++ apply nec_gen. assumption. apply Mp with [! α /\ β !].
                +++ apply Ax with (ax5 α β).
                    repeat constructor.
                    reflexivity.
                +++ apply Mp with [! [i](α /\ β) !].
                    * apply Ax with (axT i [! α /\ β !]).
                      constructor.
                      apply T_axT.
                      reflexivity.
                    * assumption.
            ++ apply nec_gen. assumption. apply Mp with [! α /\ β !].
                +++ apply Ax with (ax6 α β).
                    repeat constructor.
                    reflexivity.
                +++ apply Mp with [! [i](α /\ β) !].
                    * apply Ax with (axT i [! α /\ β !]).
                        constructor.
                        apply T_axT.
                        reflexivity.
                    * assumption.
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

    Lemma nec_or_distribution : forall Γ α β i, Boxed Γ i -> (S4 i; Γ |-- [! [i]α \/ [i]β !]) <-> (S4 i; Γ |-- [! [i](α \/ β) !]).
    Proof.
        intros Γ α β i H₁.
        split.
        + intros H₂. apply nec_gen. assumption. apply Mp with [! [i]α \/ [i]β !].
            ++ apply Mp with [! [i]β -> β !].
                +++ apply Mp with [! [i]α -> α !].
                    * apply or_exchange. repeat constructor. assumption.
                    * apply Ax with (axT i α). constructor. apply T_axT. reflexivity.
                +++ apply Ax with (axT i β). constructor. apply T_axT. reflexivity.
            ++ assumption.
        + intros H₂. admit.
    Admitted.

    Definition Squared (Γ : theory) i := forall α, Γ α -> exists β, α = square β i.
    Definition Circled (Γ : theory) i := forall α, Γ α -> exists β, α = Box i (circle β i).

    Lemma strict_deduction : forall Γ α β i, Boxed Γ i -> (S4 i ; [α] ∪ Γ |-- β) -> S4 i ; Γ |-- [! [i](α -> β) !].
    Proof.
        intros Γ α β i H₁ H₂.
        apply nec_gen.
        + assumption.
        + apply modal_deduction.
            ++ repeat constructor. assumption.
            ++ assumption.
    Qed.

    Theorem equivalence : forall (α : Sentence) i, S4 i ; Empty |-- [! [i](α ! i) <-> (α ? i) !].
    Proof.
        intros α i.
        induction α as [ | | | | α H₁ β H₂].
        + apply splitting. repeat constructor. assumption. split.
            ++ apply Ax with (axT i (square ⊥ i)).
                +++ apply S4_T, T_axT.
                +++ reflexivity.
            ++ admit.
        + apply splitting. repeat constructor. assumption. split.
            ++ admit.
            ++ admit.
        + admit.
        + admit.
        + apply splitting. repeat constructor. assumption. split.
            ++ apply modal_deduction.
                +++ repeat constructor. assumption.
                +++ apply nec_gen.
                    * intros γ H₃. inversion H₃ as [H₄ | H₄]. exists (circle (α → β) i). inversion H₄. reflexivity. contradiction.
                    * fold square. apply modal_syllogism with [! [i](β ! i) !].
                        ** repeat constructor.
                        ** repeat constructor.
                        ** apply modal_syllogism with [! [i](α ! i) !].
                            *** repeat constructor.
                            *** repeat constructor.
                            *** apply modal_ax6 with [! [i](α ! i) -> (α ? i) !].
                                - repeat constructor.
                                - apply derive_weak with ∅. right. assumption. assumption.
                            *** apply modal_syllogism with [! [i][i](α ! i) !].
                                - repeat constructor.
                                - repeat constructor.
                                - apply Ax with (axK4 i [! α ! i !]).
                                    -- apply S4_axK4.
                                    -- reflexivity.
                                - apply modal_axK.
                                    -- constructor. constructor. apply K_axK.
                                    -- apply Prem. left. reflexivity.
                        ** apply modal_ax5 with [! (β ? i) -> [i](β ! i) !].
                            *** repeat constructor.
                            *** apply derive_weak with ∅. right. assumption. assumption.
            ++ apply modal_deduction.
                +++ repeat constructor. assumption.
                +++ apply strict_deduction.
                    * intros γ H₃. exists [! (α ? i) -> (β ? i) !]. inversion H₃.
                        ** inversion H. reflexivity.
                        ** contradiction.
                    * fold circle. apply Mp with [! [i](β ! i)!].
                        ** apply Ax with (axT i [! (β ! i) !]).
                            *** constructor. apply T_axT.
                            *** reflexivity.
                        ** apply Mp with [! (β ? i) !].
                            *** apply Mp with [! [i](β ! i) <-> (β ? i) !].
                                - apply Ax with (ax6 [! [i](β ! i) -> (β ? i) !] [! (β ? i) -> [i](β ! i) !]).
                                    -- repeat constructor.
                                    -- simpl. reflexivity.
                                - apply derive_weak with ∅. repeat constructor. contradiction. assumption.
                            *** 

    apply splitting. repeat constructor. assumption. split.
    + intros. induction α as [ | a | α H₁ β H₂ | α H₁ β H₂ | α H₁ β H₂].
        ++ apply Ax with (axT i (square ⊥ i)).
            +++ apply S4_T, T_axT.
            +++ reflexivity.
        ++ apply derive_identity. repeat constructor. assumption.
        ++ apply modal_deduction. repeat constructor. assumption. apply Mp with (square β i).
            +++ apply Mp with (square α i).
                * apply Ax with (ax4 (square α i) (square β i)).
                    ** repeat constructor.
                    ** reflexivity.
                * apply Mp with (Box i (circle α i)).
                    ** apply derive_weak with ∅. left. contradiction. assumption.
                    ** apply Mp with (And (Box i (circle α i)) (Box i (circle β i))).
                        *** apply Ax with (ax5 (Box i (circle α i)) (Box i (circle β i))).
                            repeat constructor.
                            reflexivity.
                        *** apply nec_and_distribution.
                            - intros γ H₃.
                              inversion H₃ as [H₄ | H₄]. 
                              exists (circle (α ∧ β) i).
                              inversion H₄ as [H₅]. reflexivity. contradiction.
                            - apply Prem. left. reflexivity.
            +++ apply Mp with (Box i (circle β i)).
                * apply derive_weak with ∅. left. contradiction. assumption.
                * apply Mp with (And (Box i (circle α i)) (Box i (circle β i))).
                    ** apply Ax with (ax6 (Box i (circle α i)) (Box i (circle β i))).
                       repeat constructor.
                       reflexivity.
                    ** apply nec_and_distribution.
                        *** intros γ H₃.
                            inversion H₃ as [H₄ | H₄].
                            exists (circle (α ∧ β) i).
                            inversion H₄ as [H₅].
                            reflexivity.
                            contradiction.
                        *** apply Prem.
                            left.
                            reflexivity.
        ++ apply modal_deduction.
            +++ repeat constructor. assumption.
            +++ apply Mp with (circle (α ∨ β) i).
                * apply Mp with (Implies (Box i (circle β i)) (square β i)).
                    ** apply Mp with (Implies (Box i (circle α i)) (square α i)).
                        *** apply or_exchange. repeat constructor. assumption.
                        *** apply derive_weak with ∅. right. assumption. assumption.
                    ** apply derive_weak with ∅. right. assumption. assumption.
                * apply Mp with (Box i (circle (α ∨ β) i)).
                    ** apply Ax with (axT i (circle (α ∨ β) i)).
                        *** apply S4_T, T_axT.
                        *** reflexivity.
                    ** apply Prem. left. reflexivity.
        ++ apply modal_deduction.
            +++ repeat constructor. assumption.
            +++ apply nec_gen.
                * intros γ H₃. inversion H₃ as [H₄ | H₄]. exists (circle (α → β) i). inversion H₄. reflexivity. contradiction.
                * fold square. apply modal_syllogism with (Box i (circle β i)).
                    ** repeat constructor.
                    ** repeat constructor.
                    ** apply modal_syllogism with (Box i (circle α i)).
                        *** repeat constructor.
                        *** repeat constructor.
                        *** 
    + intros. induction α as [ | a | α H₁ β H₂ | α H₁ β H₂ | α H₁ β H₂].
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
    Admitted.

    (* Theorem equivalence : forall Γ α i, (Circled Γ i -> S4 i ; Γ |-- circle α i) <-> (Squared Γ i -> S4 i ; Γ |-- square α i).
    Proof.
        intros. split.
        + intros H₁ H₂.
          induction α.
          ++ apply H₁. unfold Circled. intros α H₃. *)

    Lemma left_or : forall Γ α β γ i, (S4 i; Extend α Γ |-- γ) -> (S4 i; Extend β Γ |-- γ) -> (S4 i; Extend [! α \/ β !] Γ |-- γ).
    Proof.
        intros.
        apply Mp with [! α \/ β !].
        + apply Mp with [! β -> γ !].
            ++ apply Mp with [! α -> γ !].
                +++ apply Ax with (ax9 α β γ). repeat constructor. reflexivity.
                +++ apply derive_weak with Γ. right. assumption. apply modal_deduction. repeat constructor. assumption. assumption.
            ++ apply derive_weak with Γ. right. assumption. apply modal_deduction. repeat constructor. assumption. assumption.
        + apply Prem. left. reflexivity.
    Qed.

    Lemma square_nec : forall Γ α i, S4 i ; Γ |-- Implies (square α i) (Box i (square α i)).
    Proof.
        intros.
        induction α as [ | | α H₁ β H₂ | | ].
        + admit.
        + apply modal_axK4. apply S4_axK4.
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
        + apply modal_deduction. repeat constructor. assumption.
          apply Mp with (Or (Box i (square α1 i)) (Box i (square α2 i))).
              ++ admit.
              ++ apply Mp with (Or (square α1 i) (square α2 i)).
                    +++ apply Mp with (Implies (square α2 i) (Box i (square α2 i))).
                        * apply Mp with (Implies (square α1 i) (Box i (square α1 i))).
                            ** apply or_exchange. repeat constructor. assumption.
                            ** apply derive_weak with Γ. right. assumption. assumption.
                        * apply derive_weak with Γ. right. assumption. assumption.
                    +++ apply Prem. left. reflexivity.
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
            ++ fold square. repeat (apply strict_deduction).
                +++ intros φ H. destruct H.
                    * inversion H. exists (Implies (square α i) (Box i (Implies (square β i) (square γ i)))). reflexivity.
                    * contradiction.
                +++ intros φ H. destruct H as [H | [H | H]].
                    * inversion H. exists (Implies (square α i) (square β i)). reflexivity.
                    * inversion H. exists (Implies (square α i) (Box i (Implies (square β i) (square γ i)))). reflexivity.
                    * contradiction.
                +++ apply strict_ponens with (square β i).
                    * apply strict_ponens with (square α i).
                        ** apply Prem. right. right. left. reflexivity.
                        ** apply Prem. left. reflexivity.
                    * apply strict_ponens with (square α i).
                        ** apply Prem. right. left. reflexivity.
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
            ++ fold square. repeat (apply strict_deduction).
                +++ intros φ H.
                    destruct H as [H | H]. inversion H. exists (Implies (square α i) (square γ i)). reflexivity. contradiction.
                +++ intros φ H.
                    destruct H as [H | H]. inversion H. exists (Implies (square β i) (square γ i)). reflexivity. 
                    destruct H as [H | H]. inversion H. exists (Implies (square α i) (square γ i)). reflexivity. contradiction.
                +++ apply Mp with (Or (square α i) (square β i)).
                   * apply Mp with (Implies (square β i) (square γ i)).
                       ** apply Mp with (Implies (square α i) ((square γ i))).
                           *** apply Ax with (ax9 (square α i) (square β i) (square γ i)).
                               - repeat constructor.
                               - reflexivity.
                           *** apply Mp with (Box i (Implies (square α i) (square γ i))).
                               - apply Ax with (axT i (Implies (square α i) (square γ i))).
                                   -- apply S4_T, T_axT.
                                   -- reflexivity.
                               - apply Prem. right. right. left. reflexivity.
                       ** apply Mp with (Box i (Implies (square β i) (square γ i))).
                           *** apply Ax with (axT i (Implies (square β i) (square γ i))).
                               - apply S4_T, T_axT.
                               - reflexivity.
                           *** apply Prem. right. left. reflexivity.
                    * apply Prem. left. reflexivity. 
        + apply Nec. apply modal_deduction.
            ++ repeat constructor. assumption.
            ++ apply consistency_deduction.
                +++ repeat constructor. assumption.
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