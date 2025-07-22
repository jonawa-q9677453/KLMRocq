Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import semantic.
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
      In Formula Γ (p ↔ q) -> 
      CumulCons 𝐊 Γ p r -> 
      CumulCons 𝐊 Γ q r
      
  | RW : forall 𝐊 Γ p q r, 
      In Formula Γ (p → q) -> 
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
