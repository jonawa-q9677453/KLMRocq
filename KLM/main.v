Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.

Require Import KLM_Base.
Require Import KLM_Cumulative.
Require Import KLM_Semantics.
Require Import KLM_Soundness.
Export KLM_Soundness_M.
Require Import KLM_Completeness.
Export KLM_Completeness_M.

Example simple_model : CumulModel.
  apply (Build_CumulModel nat 
                         (fun n => fun f => match f with Var 0 => true | _ => false end)
                         (fun n m => n < m)).
Defined.

Example simple_reflexivity : 
  forall Γ, Γ ~ (Var 0) |~ (Var 0).
Proof.
  intros.
  solve_cumul.
Qed.

Lemma example_reflexivity (𝐊 : KnowledgeBase) (p : Formula) :
  𝐊 |≈ p |~ p.
Proof.
  solve_cumul.
Qed.

Example simple_CM : 
  forall Γ p q r, 
    Γ ~ p |~ q -> 
    Γ ~ p |~ r -> 
    Γ ~ (p ∧ q) |~ r.
Proof.
  intros Γ p q r H_pq H_pr.
  apply CM.
  - exact H_pq.
  - exact H_pr.
Qed.

Example CM_RW_example : 
  forall Γ p q r s, 
    In Formula Γ (r → s) ->
    Γ ~ p |~ q ->
    Γ ~ p |~ r ->
    Γ ~ (p ∧ q) |~ s.
Proof.
  intros Γ p q r s H_impl H_p_q H_p_r.
  apply CM.
  - exact H_p_q.
  - apply RW with r.
    + exact H_impl.
    + exact H_p_r.
Qed.

Example k_direct_usage :
  forall 𝐊 Γ p q,
    InKB 𝐊 p q ->
    CumulCons 𝐊 Γ p q.
Proof.
  intros 𝐊 Γ p q H_pq.
  apply Base.
  exact H_pq.
Qed.

Example k_cautious_monotonicity :
  forall 𝐊 Γ p q r,
    InKB 𝐊 p q ->
    InKB 𝐊 p r ->
    CumulCons 𝐊 Γ (p ∧ q) r.
Proof.
  intros 𝐊 Γ p q r H_pq H_pr.
  apply CM.
  - apply Base. exact H_pq.
  - apply Base. exact H_pr.
Qed.

(* 3. Cut mit K-Assertions *)
Example k_cut_example :
  forall 𝐊 Γ p q r,
    InKB 𝐊 (p ∧ q) r ->
    InKB 𝐊 p q ->
    CumulCons 𝐊 Γ p r.
Proof.
  intros 𝐊 Γ p q r H_conj_r H_p_q.
  apply Cut with q.
  - apply Base. exact H_conj_r.  (* (p ∧ q) |~ r *)
  - apply Base. exact H_p_q.     (* p |~ q *)
Qed.

Example k_reflexivity :
  forall 𝐊 Γ p,
    CumulCons 𝐊 Γ p p.
Proof.
  intros 𝐊 Γ p.
  apply Ref.
Qed.

Example k_with_gamma_example :
  forall 𝐊 Γ p q r,
    InKB 𝐊 p q ->                 (* p |~ q from 𝐊 *)
    In Formula Γ (q → r) ->       (* q → r from Γ *)
    CumulCons 𝐊 Γ p r.            (* p |~ r combined *)
Proof.
  intros 𝐊 Γ p q r H_pq H_qr.
  apply RW with q.
  - exact H_qr.         (* q → r aus Γ *)
  - apply Base.
    exact H_pq.         (* p |~ q aus 𝐊 *)
Qed.

Example tweety_penguin :
  forall Γ,
    Γ ~ (Var 0) |~ (Var 1) ->       					(* Bird |~ flys *)
    In Formula Γ ((Var 2) → (Var 0)) ->  				(* Penguin → Bird *)
    In Formula Γ ((Var 2) → ¬(Var 1)) -> 				(* Penguin → ¬fly *)
    Γ ~ (Var 2) |~ ¬(Var 1).        					(* Penguin |~ ¬fly *)
Proof.
  intros Γ H_bird_fly H_penguin_bird H_penguin_not_fly.
  apply RW with (Var 2).
  - exact H_penguin_not_fly.
  - apply Ref.
Qed.

Definition Quaker := Var 0.
Definition Republican := Var 1.  
Definition Pacifist := Var 2.

Definition NixonKB : Ensemble Formula := 
  fun f => f = (Quaker → Pacifist) \/ 
           f = (Republican → ¬Pacifist) \/
           f = Quaker \/
           f = Republican.

Lemma quaker_pacifist_in_kb : In Formula NixonKB (Quaker → Pacifist).
Proof.
  unfold NixonKB. left. reflexivity.
Qed.

Lemma republican_not_pacifist_in_kb : In Formula NixonKB (Republican → ¬Pacifist).
Proof.
  unfold NixonKB. right. left. reflexivity.
Qed.

Lemma quaker_in_kb : In Formula NixonKB Quaker.
Proof.
  unfold NixonKB. right. right. left. reflexivity.
Qed.

Lemma republican_in_kb : In Formula NixonKB Republican.
Proof.
  unfold NixonKB. right. right. right. reflexivity.
Qed.

Example quakers_are_pacifists :
  NixonKB ~ Quaker |~ Pacifist.
Proof.
  apply RW with Quaker.
  - apply quaker_pacifist_in_kb.
  - apply Ref.
Qed.

Example republicans_not_pacifists :
  NixonKB ~ Republican |~ ¬Pacifist.
Proof.
  apply RW with Republican.
  - apply republican_not_pacifist_in_kb.
  - apply Ref.
Qed.

Example nixon_conflict :
  In Formula NixonKB Quaker /\
  In Formula NixonKB Republican /\
  (NixonKB ~ Quaker |~ Pacifist) /\
  (NixonKB ~ Republican |~ ¬Pacifist).
Proof.
  repeat split.
  - apply quaker_in_kb.
  - apply republican_in_kb.
  - apply quakers_are_pacifists.
  - apply republicans_not_pacifists.
Qed.

(* Conditional Assertions KB *)
Definition BirdKB : KnowledgeBase := 
  fun ca => ca = CA (Var 0) (Var 1) \/     (* Birds typically fly *)
            ca = CA (Var 2) (¬(Var 1)).    (* Penguins typically don't fly *)

Lemma bird_flies_in_kb : InKB BirdKB (Var 0) (Var 1).
Proof.
  unfold InKB, BirdKB. left. reflexivity.
Qed.

Lemma penguin_not_flies_in_kb : InKB BirdKB (Var 2) (¬(Var 1)).
Proof.
  unfold InKB, BirdKB. right. reflexivity.
Qed.

Example direct_kb_usage_birds :
  BirdKB |≈ (Var 0) |~ (Var 1).    (* Birds |~ fly *)
Proof.
  apply Base.
  apply bird_flies_in_kb. 
Qed.

Example direct_kb_usage_penguins :
  BirdKB |≈ (Var 2) |~ ¬(Var 1).   (* Penguins |~ ¬fly *)
Proof.
  apply Base.
  apply penguin_not_flies_in_kb.
Qed.

Definition BirdContext : Ensemble Formula :=
  fun f => f = ((Var 2) → (Var 0)).

Example kb_with_classical_reasoning_alt :
  CumulCons BirdKB BirdContext (Var 2) (Var 0).
Proof.
  apply RW with (Var 2).
  - unfold BirdContext. reflexivity.
  - apply Ref.
Qed.

Example empty_kb_reasoning_test :
  BirdContext ~ (Var 2) |~ (Var 0).
Proof.
  apply RW with (Var 2).
  - unfold BirdContext. reflexivity.
  - apply Ref.
Qed.

Example full_power_example :
  CumulCons BirdKB BirdContext (Var 2) ¬(Var 1).
Proof.
  apply Base.
  apply penguin_not_flies_in_kb.
Qed.

Theorem klm_theorem :
  forall (𝐊 : KnowledgeBase) (Γ : Ensemble Formula) (p q : Formula),
	(𝐊⊕Γ ⊢ p |~ q) <-> (𝐊⊕Γ ⊨ p |~w q).
Proof.
  intros 𝐊 Γ p q.
  split.
  - apply soundness_klm.
  - apply completeness_klm.
Qed.
