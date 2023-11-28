From Coq Require Export String.

Inductive bool : Type :=
| true
| false. 

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


Definition negb' (b:bool) : bool := if b then false else true.
Definition andb' (b1:bool) (b2:bool) : bool := if b1 then b2 else false.
Definition orb' (b1: bool) (b2:bool) : bool := if b2 then true else b2.

(* Exercise *)
Definition nandb (b1: bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.  

(* Types *)
Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p: rgb).

Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c: color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
(* (the wildcard pattern _ has the same effect as the _dummy_ pattern variable p in the
definition of monochrome) *)


(* Modules *)
Module TuplePlayground.
  Inductive bit : Type := | B1 | B0.
  Inductive nybble  : Type := | bits (b0 b1 b2 b3 : bit).

  Definition all_zero (nb: nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.

  Compute (all_zero (bits B1 B0 B1 B0)). 
End TuplePlayground.

Module NatPlayground.
  Inductive nat : Type := | O | S (n : nat).
  Inductive otherNat : Type := | stop | tick (foo: otherNat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
  (* computation rules / can be simplified *)
End NatPlayground.

Fixpoint even (n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool := negb (even n).

Example test_odd1: odd 1 = true.
Proof. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. reflexivity. Qed.

Module NatPlayground2.
  Fixpoint plus (n: nat) (m: nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Fixpoint mult (n m: nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
End NatPlayground2.
Fixpoint exp (base power: nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.
  
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
        | O => true
        | S m' => false
        end
  | S n' => match m with
           | O => false
           | S m' => eqb n' m'
           end
  end.

Fixpoint leb (n m: nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
           | O => false
           | S m' => leb n' m'
           end
  end.

Example test_leb1: leb 2 2 = true.
Proof. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. reflexivity. Qed.

(* Exercise ltb *)
Definition ltb (n m : nat) : bool :=
  if (eqb n m) then false
    else if (leb n m) then true
         else false.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. reflexivity. Qed.


(* Proof by Rewriting exercise *)
Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
  Qed.

Check mult_n_O.
Check mult_n_Sm.
(* use mult_n_Sm and mult_n_O to prove the following theorem *)
Theorem mutl_n_1: forall p : nat, p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
  Qed.

(* Proof by case analysis: using /destruct/, it generates two subgoals,
 then prove separately *)

Theorem plus_1_neq_0 : forall n : nat, (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_1_neq_0' : forall n : nat, (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c,
    andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
            


  
Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + simpl. intros H. rewrite -> H. reflexivity.
  - destruct c eqn:Ec.
    + simpl. intros H. reflexivity.
    + simpl. intros H. rewrite -> H. reflexivity.
Qed.

(* More Exercises TBC*)
