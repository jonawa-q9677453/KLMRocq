Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import base_pc.
Require Import semantic.
Require Import KLM_Base.
Require Import KLM_Cumulative.
Require Import KLM_Semantics.

Module KLM_Soundness_M.

Lemma soundness_base :
  forall (𝐊 : KnowledgeBase) (Γ : Ensemble Formula) (p q : Formula),
    InKB 𝐊 p q ->
    forall model, SatisfiesKnowledgeBases model 𝐊 Γ -> model : p |~w q.
Proof.
  intros 𝐊 Γ p q H_in_kb model H_satisfies.
  unfold SatisfiesKnowledgeBases in H_satisfies.
  destruct H_satisfies as [H_conditional _].
  unfold SatisfiesConditionalKB in H_conditional.
  apply H_conditional.
  exact H_in_kb.
Qed.

Lemma soundness_reflexivity :
  forall (model : CumulModel) (formula : Formula),
    (model : formula |~w formula).
Proof.
  unfold SemanticEntails, MinimalElements.
  intros model formula state [H_satisfies _].
  exact H_satisfies.
Qed.

Lemma soundness_LLE :
  forall (model : CumulModel) (p q r : Formula),
    (forall state, entails (Labeling model state) p <-> entails (Labeling model state) q) ->
    (model : p |~w r) ->
    (model : q |~w r).
Proof.
  unfold SemanticEntails, MinimalElements.
  intros model p q r H_equiv H_entails state [H_q H_minimal].
  assert (H_p : entails (Labeling model state) p).
  apply H_equiv; assumption.
  apply H_entails.
  split.
  - assumption.
  - intro H_exists.
    destruct H_exists as [state' [H_p' H_pref]].
    
    exfalso.
    apply H_minimal.
    exists state'.
    split.
    + apply H_equiv; assumption.
    + assumption.
Qed.

Lemma soundness_RW :
  forall (model : CumulModel) (p q r : Formula),
    (forall state, entails (Labeling model state) p -> entails (Labeling model state) q) ->
    (model : r |~w p) ->
    (model : r |~w q).
Proof.
  unfold SemanticEntails, MinimalElements.
  intros model p q r H_imp H_entails state H_minimal.
  apply H_imp.
  apply H_entails; assumption.
Qed.

Lemma soundness_Cut :
  forall (model : CumulModel) (p q r : Formula),
    (model : (p ∧ q)  |~w r) ->
    (model : p |~w q) ->
    (model : p |~w r).
Proof.
  unfold SemanticEntails, MinimalElements.
  intros model p q r H_conj_entails H_p_entails_q state [H_p H_minimal].
  assert (H_q : entails (Labeling model state) q).
  apply H_p_entails_q.
  split; [assumption | exact H_minimal].
  
  apply H_conj_entails.
  split.
  
  - rewrite entails_conjunction.
    split; assumption.
  
  - intro H_exists.
    destruct H_exists as [state' [H_conj' H_pref]].
    rewrite entails_conjunction in H_conj'.
    destruct H_conj' as [H_p' _].
    exfalso.
    apply H_minimal.
    exists state'.
    split; assumption.
Qed.

Lemma soundness_CM :
  forall (model : CumulModel) (p q r : Formula),
    (model : p |~w q) ->
    (model : p |~w r) ->
    (model : (p ∧ q) |~w r).
Proof.
  unfold SemanticEntails, MinimalElements.
  intros model p q r H_p_q H_p_r state [H_conj H_minimal].
  
  rewrite entails_conjunction in H_conj.
  destruct H_conj as [H_p H_q].
  
  assert (H_p_in_state : entails (Labeling model state) p).
  { exact H_p. }
  
  destruct (smoothness model p state H_p) as [min_state [H_min_p [H_pref_or_eq H_min_element]]].
  
  unfold MinimalElements in H_min_element.
  destruct H_min_element as [H_min_p_satisfies H_min_minimal].
  
  assert (H_min_q : entails (Labeling model min_state) q).
  apply H_p_q; split; [assumption | exact H_min_minimal].
  
  assert (H_min_conj : entails (Labeling model min_state) (p ∧ q)).
  apply entails_conjunction; split; assumption.
  
  destruct H_pref_or_eq as [H_pref | H_eq].
  
  - (* Fall 1: min_state < state *)
    exfalso.
    apply H_minimal.
    exists min_state.
    split; [assumption | assumption].
  
  - (* Fall 2: min_state = state *)
    subst min_state.
    apply H_p_r.
    split; [assumption | exact H_min_minimal].
Qed.

Theorem soundness_klm :
  forall (𝐊 : KnowledgeBase) (Γ : Ensemble Formula) (p q : Formula),
    (𝐊⊕Γ ⊢ p |~ q) -> (𝐊⊕Γ ⊨ p |~w q).
Proof.
  intros 𝐊 Γ p q H_cons.
  unfold CumulativeModelEntails.
  intros model H_satisfies.
  
  induction H_cons.
  
  - (* Ref *)
    apply soundness_reflexivity.
   
  - (* LLE *)
    apply soundness_LLE with p.
    + intros state.
      unfold SatisfiesKnowledgeBases in H_satisfies.
      destruct H_satisfies as [_ H_classical].
      unfold SatisfiesClassicalKB in H_classical.
      assert (H_equiv : entails (Labeling model state) (p ↔ q)).
      { apply H_classical. exact H. }
      apply entails_equivalence in H_equiv.
      assumption.
    + apply IHH_cons. exact H_satisfies.
    
  - (* RW *)
    apply soundness_RW with p.
    + intros state H_p.
      unfold SatisfiesKnowledgeBases in H_satisfies.
      destruct H_satisfies as [_ H_classical].
      assert (H_impl : entails (Labeling model state) (p → q)).
      { apply H_classical. exact H. }
      simpl in H_impl.
      apply H_impl. exact H_p.
    + apply IHH_cons. exact H_satisfies.
    
  - (* Cut *)
    apply soundness_Cut with q.
    + apply IHH_cons1. exact H_satisfies.
    + apply IHH_cons2. exact H_satisfies.
    
  - (* CM *)
    apply soundness_CM.
    + apply IHH_cons1. exact H_satisfies.
    + apply IHH_cons2. exact H_satisfies.
    
  - (* Base *)
    unfold SatisfiesKnowledgeBases in H_satisfies.
    destruct H_satisfies as [H_conditional _].
    unfold SatisfiesConditionalKB in H_conditional.
    apply H_conditional.
    exact H.
Qed.

End KLM_Soundness_M.
