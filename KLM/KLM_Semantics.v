Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import base_pc.
Require Import semantic.
Require Import KLM_Base.
Require Import KLM_Cumulative.

Definition Minimal {S : Type} (label : S -> Ensemble World)
  (pref : S -> S -> Prop) (formula : Formula) (state : S) : Prop :=
  entails (label state) formula /\
  ~ exists state', entails (label state') formula /\ pref state' state.

Definition Smooth {S : Type} (label : S -> Ensemble World)
  (pref : S -> S -> Prop) : Prop :=
  forall formula state,
    entails (label state) formula ->
    Minimal label pref formula state \/
    exists state', Minimal label pref formula state' /\ pref state' state.

Record CumulModel : Type := {
  States : Type;
  Labeling : States -> Ensemble World;
  PreferenceRel : States -> States -> Prop;
  labels_are_valuations : forall s v, In World (Labeling s) v -> value v;

  labels_nonempty : forall s, exists v, In World (Labeling s) v;
  smooth : Smooth Labeling PreferenceRel
}.

Definition MinimalElements (model : CumulModel) (formula : Formula) : Ensemble (States model) :=
  fun state => Minimal (Labeling model) (PreferenceRel model) formula state.

Definition SemanticEntails (model : CumulModel) (premise conclusion : Formula) : Prop :=
  forall state, In (States model) (MinimalElements model premise) state ->
                entails (Labeling model state) conclusion.

Notation "model ':' premise '|~w' conclusion" :=
  (SemanticEntails model premise conclusion) (at level 80).

Definition SatisfiesClassicalKB (model : CumulModel)
  (Γ : Ensemble Formula) : Prop :=
  forall state v, In World (Labeling model state) v ->
                  forall formula, In Formula Γ formula -> v formula = true.

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

Lemma smoothness : forall model formula state,
  entails (Labeling model state) formula ->
  exists minimal_state,
    entails (Labeling model minimal_state) formula /\
    (PreferenceRel model minimal_state state \/ minimal_state = state) /\
    In (States model) (MinimalElements model formula) minimal_state.
Proof.
  intros model formula state H.
  destruct (smooth model formula state H) as [H_min | [m [H_min H_pref]]].
  - exists state. split; [exact H | split; [right; reflexivity | exact H_min]].
  - exists m. split; [apply H_min | split; [left; exact H_pref | exact H_min]].
Qed.
