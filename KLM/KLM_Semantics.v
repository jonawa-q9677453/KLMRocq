Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import base_pc.
Require Import semantic.
Require Import KLM_Base.
Require Import KLM_Cumulative.

Record CumulModel : Type := {
  States : Type;
  Labeling : States -> State;
  PreferenceRel : States -> States -> Prop;
}.

Definition MinimalElements (model : CumulModel) (formula : Formula) : Ensemble (States model) :=
  fun state => 
    entails (Labeling model state) formula /\
    ~ exists state', entails (Labeling model state') formula /\ PreferenceRel model state' state.

Definition SemanticEntails (model : CumulModel) (premise conclusion : Formula) : Prop :=
  forall state, In (States model) (MinimalElements model premise) state -> 
                entails (Labeling model state) conclusion.

Notation "model ':' premise '|~w' conclusion" := 
  (SemanticEntails model premise conclusion) (at level 80).

Definition SatisfiesClassicalKB (model : CumulModel) 
  (Γ : Ensemble Formula) : Prop :=
  forall formula, In Formula Γ formula -> 
                 forall state, entails (Labeling model state) formula.

Definition SatisfiesConditionalKB (model : CumulModel) 
  (𝐊 : KnowledgeBase) (Γ : Ensemble Formula) : Prop :=
  forall p q, InKB 𝐊 p q -> model : p |~w q.

Definition SatisfiesKnowledgeBases (model : CumulModel) 
  (𝐊 : KnowledgeBase) (Γ : Ensemble Formula) : Prop :=
  SatisfiesConditionalKB model 𝐊 Γ /\ SatisfiesClassicalKB model Γ.

Definition CumulativeModelEntails 
  (𝐊 : KnowledgeBase) (Γ : Ensemble Formula) 
  (premise conclusion : Formula) : Prop :=
  forall model, SatisfiesKnowledgeBases model 𝐊 Γ -> model : premise |~w conclusion.

Notation "𝐊 '⊕' Γ '⊨' premise '|~w' conclusion" := 
  (CumulativeModelEntails 𝐊 Γ premise conclusion) (at level 80).

Definition SatisfiesKnowledgeBase (model : CumulModel) (Γ : Ensemble Formula) : Prop :=
  SatisfiesClassicalKB model Γ.

Axiom smoothness : forall model formula state, 
  entails (Labeling model state) formula ->
  exists minimal_state, 
    entails (Labeling model minimal_state) formula /\ 
    (PreferenceRel model minimal_state state \/ minimal_state = state) /\
    In (States model) (MinimalElements model formula) minimal_state.
