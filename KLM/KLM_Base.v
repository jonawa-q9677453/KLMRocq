Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.

Definition World := Formula -> bool.

Definition entails (label : Ensemble World) (formula : Formula) : Prop :=
  forall v, In World label v -> v formula = true.

Lemma deduce_iff_semantic :
  forall Γ p, Γ ├ p <-> Γ ╞ p.
Proof.
  split.
  - apply soundness_L.
  - apply complete.
Qed.

Lemma tautology_deduce :
  forall Γ p, (forall v, value v -> v p = true) -> Γ ├ p.
Proof.
  intros Γ p H.
  apply complete.
  intros v Hv _.
  apply H; exact Hv.
Qed.

Ltac bool_normalize Hn Hc :=
  repeat (rewrite Hc in * || rewrite Hn in *).

Ltac taut :=
  let v := fresh "v" in
  let Hn := fresh "Hn" in
  let Hc := fresh "Hc" in
  intros v [Hn Hc];
  bool_normalize Hn Hc;
  repeat match goal with
         | |- context [v ?x] => destruct (v x)
         end;
  reflexivity.

Lemma value_conjunction :
  forall v p q, value v ->
    (v (p ∧ q) = true <-> (v p = true /\ v q = true)).
Proof.
  intros v p q [Hn Hc].
  bool_normalize Hn Hc.
  destruct (v p), (v q); simpl; intuition discriminate.
Qed.

Lemma value_contain :
  forall v p q, value v ->
    (v (p → q) = true <-> (v p = true -> v q = true)).
Proof.
  intros v p q [Hn Hc].
  bool_normalize Hn Hc.
  destruct (v p), (v q); simpl; intuition discriminate.
Qed.

Lemma value_equivalence :
  forall v p q, value v ->
    (v (p ↔ q) = true <-> v p = v q).
Proof.
  intros v p q [Hn Hc].
  bool_normalize Hn Hc.
  destruct (v p), (v q); simpl; intuition discriminate.
Qed.

Lemma entails_conjunction :
  forall (label : Ensemble World) p q,
    (forall v, In World label v -> value v) ->
    (entails label (p ∧ q) <-> (entails label p /\ entails label q)).
Proof.
  intros label p q H_val.
  unfold entails.
  split.
  - intro H. split; intros v Hv;
      apply (value_conjunction v p q (H_val v Hv)); auto.
  - intros [Hp Hq] v Hv.
    apply (value_conjunction v p q (H_val v Hv)); auto.
Qed.
