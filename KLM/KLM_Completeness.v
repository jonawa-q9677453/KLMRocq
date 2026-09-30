Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.
Require Import KLM_Base.
Require Import KLM_Cumulative.
Require Import KLM_Semantics.
Require Import KLM_Soundness.

Module KLM_Completeness_M.


Section Canonical.

Variable 𝐊 : KnowledgeBase.
Variable Γ : Ensemble Formula.

Notation "p |~c q" := (CumulCons 𝐊 Γ p q) (at level 80).

Definition CanonicalLabel (α : Formula) : Ensemble World :=
  fun v => value v /\
           (forall g, In Formula Γ g -> v g = true) /\
           (forall β, α |~c β -> v β = true).

Lemma canonical_entails :
  forall α β, entails (CanonicalLabel α) β <-> (α |~c β).
Proof.
  intros α β. split.
  - intro H.
    apply consequences_closed.
    apply complete.
    intros v H_val H_sat.
    apply H.
    split; [exact H_val | split].
    + intros g H_g. apply H_sat. apply UnionI. left. exact H_g.
    + intros γ H_γ. apply H_sat. apply UnionI. right. exact H_γ.
  - intros H v [_ [_ H_cons]].
    apply H_cons, H.
Qed.

Definition Bot : Formula := ¬((Var 0) → (Var 0)).

Definition Consistent (α : Formula) : Prop := ~ (α |~c Bot).

Lemma bot_entails_all : forall α β, (α |~c Bot) -> (α |~c β).
Proof.
  intros α β H.
  apply RW with Bot; [apply tautology_deduce; unfold Bot; taut | exact H].
Qed.

Lemma consistent_nonempty :
  forall α, Consistent α -> exists v, In World (CanonicalLabel α) v.
Proof.
  intros α H. apply NNPP. intro H_no. apply H.
  apply canonical_entails. intros v H_v.
  exfalso. apply H_no. exists v. exact H_v.
Qed.

Lemma consistent_back :
  forall γ α, Consistent γ -> (γ |~c α) -> Consistent α.
Proof.
  intros γ α H_γ H_ga H_a. apply H_γ.
  apply Reciprocity with α; [apply bot_entails_all; exact H_a | exact H_ga | exact H_a].
Qed.

Definition CanonicalState : Type := sig Consistent.

Definition CanonicalLabeling (s : CanonicalState) : Ensemble World :=
  CanonicalLabel (proj1_sig s).

Definition CanonicalPreferenceRel (t s : CanonicalState) : Prop :=
  (proj1_sig s |~c proj1_sig t) /\ ~ (proj1_sig t |~c proj1_sig s).

Lemma canonical_minimal :
  forall α (s : CanonicalState),
    Minimal CanonicalLabeling CanonicalPreferenceRel α s <->
    ((proj1_sig s |~c α) /\ (α |~c proj1_sig s)).
Proof.
  intros α [γ H_γ].
  unfold Minimal, CanonicalLabeling, CanonicalPreferenceRel; simpl.
  split.
  - intros [H_ent H_min].
    apply canonical_entails in H_ent.
    split; [exact H_ent |].
    apply NNPP. intro H_not.
    apply H_min. exists (exist _ α (consistent_back γ α H_γ H_ent)). simpl.
    split; [apply canonical_entails, Ref | split; assumption].
  - intros [H_ga H_ag].
    split; [apply canonical_entails; exact H_ga |].
    intros [[δ H_δc] [H_δ [H_gd H_not_dg]]]. simpl in *.
    apply canonical_entails in H_δ.
    apply H_not_dg.

    assert (H_ad : α |~c δ) by (apply Reciprocity with γ; assumption).
    apply Reciprocity with α; assumption.
Qed.

Lemma canonical_labels_valuations :
  forall s v, In World (CanonicalLabeling s) v -> value v.
Proof.
  intros s v [H _]. exact H.
Qed.

Lemma canonical_labels_nonempty :
  forall s, exists v, In World (CanonicalLabeling s) v.
Proof.
  intros [α H]. apply consistent_nonempty. exact H.
Qed.

Lemma canonical_smooth : Smooth CanonicalLabeling CanonicalPreferenceRel.
Proof.
  intros α [γ H_γ] H_ent.
  unfold CanonicalLabeling in H_ent. simpl in H_ent.
  apply canonical_entails in H_ent.
  destruct (classic (α |~c γ)) as [H_ag | H_not].
  - left. apply canonical_minimal. simpl. split; assumption.
  - right. exists (exist _ α (consistent_back γ α H_γ H_ent)). split.
    + apply canonical_minimal. simpl. split; apply Ref.
    + unfold CanonicalPreferenceRel. simpl. split; assumption.
Qed.

Definition CanonicalModel : CumulModel :=
{|
  States := CanonicalState;
  Labeling := CanonicalLabeling;
  PreferenceRel := CanonicalPreferenceRel;
  labels_are_valuations := canonical_labels_valuations;
  labels_nonempty := canonical_labels_nonempty;
  smooth := canonical_smooth
|}.

Lemma canonical_semantic_entails :
  forall α β, (CanonicalModel : α |~w β) <-> (α |~c β).
Proof.
  intros α β. split.
  - intro H.
    destruct (classic (Consistent α)) as [H_c | H_i].
    + apply canonical_entails.
      refine (H (exist _ α H_c) _).
      unfold In, MinimalElements. simpl.
      apply canonical_minimal. simpl. split; apply Ref.
    + apply bot_entails_all. apply NNPP. exact H_i.
  - intros H s H_min.
    unfold In, MinimalElements in H_min. simpl in H_min.
    apply canonical_minimal in H_min.
    destruct H_min as [H_ga H_ag].
    simpl. unfold CanonicalLabeling.
    apply canonical_entails.
    apply Reciprocity with α; assumption.
Qed.

Lemma canonical_satisfies_kbs :
  SatisfiesKnowledgeBases CanonicalModel 𝐊 Γ.
Proof.
  split.
  - intros p q H_in.
    apply canonical_semantic_entails.
    apply Base. exact H_in.
  - intros s v H_v g H_g.
    simpl in H_v. unfold CanonicalLabeling, CanonicalLabel, In in H_v.
    destruct H_v as [_ [H_Γ _]].
    apply H_Γ. exact H_g.
Qed.

End Canonical.

Theorem completeness_klm :
  forall (𝐊 : KnowledgeBase) (Γ : Ensemble Formula) (p q : Formula),
	(𝐊⊕Γ ⊨ p |~w q) -> (𝐊⊕Γ ⊢ p |~ q).
Proof.
  intros 𝐊 Γ p q H_sem.
  apply (canonical_semantic_entails 𝐊 Γ).
  apply H_sem.
  apply canonical_satisfies_kbs.
Qed.

End KLM_Completeness_M.
