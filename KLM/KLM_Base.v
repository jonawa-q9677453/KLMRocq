Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.

Definition State := Formula -> bool.

Fixpoint entails (state : State) (formula : Formula) : Prop :=
  match formula with
  | Var n => state formula = true
  | Not p => ~(entails state p)
  | Contain p1 p2 => entails state p1 -> entails state p2
  end.
  
Lemma entails_conjunction :
  forall s p q, entails s (p ∧ q) <-> (entails s p /\ entails s q).
Proof.
  intros s p q.
  simpl.
  split.
  - intro H. split.
    destruct (Classical_Prop.classic (entails s p)) as [Hp | Hnp].
    exact Hp.
    exfalso. 
     assert (Hpnq: entails s (Contain p (Not q))).
     simpl. 
     intro Hp'. 
     contradiction.
     
     apply H. exact Hpnq.
     destruct (Classical_Prop.classic (entails s q)) as [Hq | Hnq].
     exact Hq.
     exfalso. 
       assert (Hpnq: entails s (Contain p (Not q))).
       simpl. 
       intro Hp. 
       exact Hnq.
    
    apply H. exact Hpnq.
    
  - intros [Hp Hq]. 
    simpl. 
    intro Hpnq.
    assert (Hnq: ~ entails s q).
    apply Hpnq. 
    exact Hp.
    contradiction.
Qed.

Lemma entails_equivalence :
  forall s p q, entails s (p ↔ q) <-> (entails s p <-> entails s q).
Proof.
  intros s p q. 
  simpl. 
  split.
  - intro H. 
    split.
    intro Hp. 
    destruct (classic (entails s q)) as [Hq | Hnq]. 
      exact Hq. 
      exfalso. 
      assert (Hcontra: (entails s p -> entails s q) -> ~ (entails s q -> entails s p)).
        intro Hpq. 
        intro Hqp. 
        apply Hpq in Hp. 
        contradiction. 

     apply H in Hcontra. 
     contradiction. 
    
     intro Hq. 
     destruct (classic (entails s p)) as [Hp | Hnp]. 
       exact Hp. 
        exfalso. 
        assert (Hcontra: (entails s p -> entails s q) -> ~ (entails s q -> entails s p)).
          intro Hpq. 
          intro Hqp. 
          apply Hqp in Hq. 
          contradiction. 
          
      apply H in Hcontra. 
      contradiction. 
      
  - intros [Hpq Hqp]. 
    simpl. 
    intro Hcontra. 
    apply Hcontra in Hpq. 
    contradiction. 
Qed.

Axiom entails_equivalence_backup :
  forall s p q, entails s (p ↔ q) <-> (entails s p <-> entails s q).

Ltac solve_formula :=
  match goal with
  | |- Formula => constructor; solve_formula
  | |- entails _ (Var _) => simpl; reflexivity
  | |- entails _ (Not _) => simpl; intro
  | |- entails _ (Contain _ _) => simpl; intro
  | _ => auto
  end.
