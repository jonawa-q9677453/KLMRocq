(* 
   Introducing a Typ 'N' to represent natural
   numbers with two constructors 'z' for zero,
   and 'S' for successor.
*)
Inductive N : Type := 
 | z : N 
 | S : N -> N.

Inductive le : N -> N -> Prop :=
 | lez:forall x, le z x
 | leS:forall x y, le x y -> le (S x) (S y).

Inductive even : N -> Prop :=
 | even_z : even z
 | even_S : forall n, even n -> even (S (S n)).
  
    
Inductive vector (A : Type) : N -> Type :=
 | vnil : vector A z
 | vcons : forall (n : N) (x : A), vector A n -> vector A (S n).


Fixpoint le_dec (a b : N) : bool :=
  match a, b with
  | z, _ => true
  | S _, z => false
  | S p, S m => le_dec p m
  end.

Fixpoint sub (a b : N) : N :=
  match a, b with
  | z, _ => z
  | x, z => x
  | S p, S m => sub p m
  end.
  
Fixpoint add (n m : N) {struct n} : N :=
  match n with
  | z => m
  | S p => S (add p m)
  end.
  
Definition example := 
  let sum := add (S z) (S (S z)) in 
  sum.
  
Definition add_one := fun (n : N) => S n.
Definition identity_N {A : Type} (x : N) : N := x.

Notation "a '<=?' b" := (le_dec a b) (at level 70).
Notation "a 'sub' b" := (sub a b) (at level 50).

Fixpoint mul (n m : N) {struct n} : N :=
  match n with
  | z => z
  | S p => add m (mul p m)
  end.

Notation "a 'mul' b" := (mul a b) (at level 40).

Fixpoint factorial (n : N) : N :=
  match n with
  | z => S z  (* 0! = 1 *)
  | S m => n mul (factorial m)
  end.

Fixpoint div' (a b : N) {struct a} : N * N :=
  match a with
  | z => (z, z)
  | S a' =>
      match b <=? a with
      | false => (z, a)
      | true => let (q, r) := div' a' b in (S q, r) 
      end
  end.

(* 
   This is a negative example of div and does not work beacuse
   the recursive call does not reduce the argument 'a'
   in a structurally smaller way.
   That means 'a' is not guarenteed to decrease with
   each recursion.
*)
Fixpoint div (a b : N) {struct a} : N * N :=
  match b <=? a with
  | false => (z, a)
  | true  => let (q, r) := div (a sub b) b in (S q, r)
  end.
