Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import KLM_Base.

Inductive ConditionalAssertion : Type :=
| CA : Formula -> Formula -> ConditionalAssertion.

Definition KnowledgeBase : Type := Ensemble ConditionalAssertion.

Definition InKB (𝐊 : KnowledgeBase) (p q : Formula) : Prop :=
  In ConditionalAssertion 𝐊 (CA p q).

Inductive CumulCons :
  KnowledgeBase ->
  Ensemble Formula ->
  Formula -> Formula -> Prop :=
  | Ref : forall 𝐊 Γ p,
      CumulCons 𝐊 Γ p p

  | LLE : forall 𝐊 Γ p q r,
      (Γ ├ (p ↔ q)) ->
      CumulCons 𝐊 Γ p r ->
      CumulCons 𝐊 Γ q r

  | RW : forall 𝐊 Γ p q r,
      (Γ ├ (p → q)) ->
      CumulCons 𝐊 Γ r p ->
      CumulCons 𝐊 Γ r q

  | Cut : forall 𝐊 Γ p q r,
      CumulCons 𝐊 Γ (p ∧ q) r ->
      CumulCons 𝐊 Γ p q ->
      CumulCons 𝐊 Γ p r

  | CM : forall 𝐊 Γ p q r,
      CumulCons 𝐊 Γ p q ->
      CumulCons 𝐊 Γ p r ->
      CumulCons 𝐊 Γ (p ∧ q) r

  | Base : forall 𝐊 Γ p q,
      InKB 𝐊 p q ->
      CumulCons 𝐊 Γ p q.

Notation "𝐊 '⊕' Γ '⊢' p '|~' q" := (CumulCons 𝐊 Γ p q) (at level 80).
Notation "𝐊 '|≈' p '|~' q" := (CumulCons 𝐊 (Empty_set Formula) p q) (at level 80).

Definition EmptyKB : KnowledgeBase := fun _ => False.
Notation "Γ '~' p '|~' q" := (CumulCons EmptyKB Γ p q) (at level 80).

Ltac solve_cumul :=
  match goal with
  | |- CumulCons _ _ _ _ =>
      first [
        apply Base; assumption |
        apply Ref |
        apply CM; solve_cumul |
        apply Cut with ?X; solve_cumul |
        constructor; solve_cumul
      ]
  | _ => try assumption
  end.


Section Derived.

Variable 𝐊 : KnowledgeBase.
Variable Γ : Ensemble Formula.

Lemma Supra : forall p q,
  (Γ ├ (p → q)) -> CumulCons 𝐊 Γ p q.
Proof.
  intros p q H.
  apply RW with p; [exact H | apply Ref].
Qed.

Lemma Supra_taut : forall p q,
  (forall v, value v -> v (p → q) = true) -> CumulCons 𝐊 Γ p q.
Proof.
  intros p q H.
  apply Supra, tautology_deduce, H.
Qed.

Lemma And : forall p q r,
  CumulCons 𝐊 Γ p q ->
  CumulCons 𝐊 Γ p r ->
  CumulCons 𝐊 Γ p (q ∧ r).
Proof.
  intros p q r Hq Hr.
  assert (H1 : CumulCons 𝐊 Γ (p ∧ q) r) by (apply CM; assumption).
  assert (H2 : CumulCons 𝐊 Γ ((p ∧ q) ∧ r) (q ∧ r))
    by (apply Supra_taut; taut).
  assert (H3 : CumulCons 𝐊 Γ (p ∧ q) (q ∧ r))
    by (apply Cut with r; assumption).
  apply Cut with q; assumption.
Qed.

Lemma Reciprocity : forall p q r,
  CumulCons 𝐊 Γ p q ->
  CumulCons 𝐊 Γ q p ->
  CumulCons 𝐊 Γ p r ->
  CumulCons 𝐊 Γ q r.
Proof.
  intros p q r Hpq Hqp Hpr.
  assert (H1 : CumulCons 𝐊 Γ (p ∧ q) r) by (apply CM; assumption).
  assert (H2 : CumulCons 𝐊 Γ (q ∧ p) r).
  { apply LLE with (p ∧ q); [apply tautology_deduce; taut | exact H1]. }
  apply Cut with p; assumption.
Qed.

Definition Consequences (p : Formula) : Ensemble Formula :=
  fun q => CumulCons 𝐊 Γ p q.

Lemma consequences_closed : forall p q,
  (Γ ∪ Consequences p ├ q) -> CumulCons 𝐊 Γ p q.
Proof.
  intros p q H.
  induction H as [x Hx | x y | x y z | x y | x y _ IHxy _ IHx].
  - apply UnionI in Hx. destruct Hx as [Hx | Hx].
    + apply Supra. apply MP with x; [apply L1 | apply L0; exact Hx].
    + exact Hx.
  - apply Supra_taut; taut.
  - apply Supra_taut; taut.
  - apply Supra_taut; taut.
  - apply RW with ((x → y) ∧ x).
    + apply tautology_deduce; taut.
    + apply And; assumption.
Qed.

End Derived.
