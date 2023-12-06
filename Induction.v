From LF Require Export Basics.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity. (* 0 + 0 = 0 *)
  - simpl. (* S n' + 0 = S n' *)
    rewrite -> IHn'.
    reflexivity.   
Qed.

Theorem mul_0_r : forall n: nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m:nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - reflexivity.  
  - simpl. (* S (S n' + m) = S n' + S m *)
    rewrite -> IHn'. (* S (S (n' + m)) = S (n' + S m)  *)
    reflexivity. 
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n  as [|n' IHn'].
  - simpl.
    rewrite ->  add_0_r.
    reflexivity.
  - simpl. (* S n' + m = m + S n' *)
    rewrite -> IHn'. (* S (n' + m) = m + S n' *)
    rewrite -> plus_n_Sm. (* S (m + n') = m + S n' *)
    reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl.
    rewrite -> add_comm.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise double_plus *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus: forall n, double n = n + n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

(* Exercise eqb_refl *)
Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise even_S optional *)
Lemma dbl_negb : forall b : bool, negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.


Theorem even_S : forall n : nat,
    even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. (* even (S (S n')) = negb (even (S n')) *)
    simpl.
    rewrite -> dbl_negb.
    reflexivity.
Qed.
(* Proofs within proofs *)

(* _Informal proofs are algorithms; formal proofs are code *)

(* More Exercises TBC*)
Theorem add_shuffle3 : forall n m p : nat, n + (m + p) = m + (n + p).
Proof. (* use assert, not induction *)
  intros.
  Abort.

Check mult_n_Sm.
Lemma mult_n_Sm' : forall n m: nat, n * m + n = n * S m.
Proof.
  intros n m.
  induction n.
  induction m.
  - reflexivity.
  - reflexivity.
  - rewrite <- plus_n_Sm.
    simpl.
    rewrite <- IHn.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mul_comm : forall m n: nat, m * n = n * m.
Proof.
  intros m n.
  induction m.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> mul_0_r.
    reflexivity.
  - simpl.
    rewrite <- mult_n_Sm'.
    rewrite -> IHm.
    rewrite -> add_comm.
    reflexivity.
Qed.


Check leb.
Theorem plus_leb_compat_l : forall n m p: nat, n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros.
  induction p.
  - simpl.
    apply H.
  - simpl.
    apply IHp.
Qed.

(* more exercises *)
Theorem leb_refl : forall n: nat, (n <=? n) = true.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem zero_neqb_S : forall n: nat, 0 =? (S n) = false.
Proof.
  intros.
  induction n.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_false_r : forall b: bool, andb b false = false.
Proof.
  intros.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0 : forall n: nat, (S n) =? 0 = false.
Proof.
  intros.
  induction n.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_1_l : forall n: nat, 1 * n = n.
Proof.
  intros.
  destruct n.
  - reflexivity.
  - simpl. rewrite add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros.
  destruct c.
  - destruct b.
    + reflexivity.
    + reflexivity.
  - destruct b.
    + reflexivity.
    + reflexivity.
Qed.

Print add_comm.

Require Import Arith.
Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction p.
  - repeat rewrite mul_0_r.
    reflexivity.
  - repeat rewrite <- mult_n_Sm'.
    rewrite -> IHp.
    repeat rewrite -> add_assoc.
    ring. (* do not know exactly how, but it works. *)
Qed.

Theorem mult_assoc : forall n m p: nat, n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    rewrite ->  mult_plus_distr_r.
    reflexivity.
Qed.

(* nat to bin and back to nat *)
Inductive bin : Type := | Z | B0 (n : bin) | B1 ( n: bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m1 => B1 m1
  | B1 m1 => B0 (incr m1)
  end.

Fixpoint bin_to_nat (m: bin) : nat :=
  match m with
  | Z => O
  | B1 Z => S O
  | B0 m' =>   (bin_to_nat m') + (bin_to_nat m')
  | B1 m' => S ((bin_to_nat m') + (bin_to_nat m'))
  end.

Theorem bin_to_nat_pres_incr : forall b : bin, bin_to_nat(incr b) = 1 + bin_to_nat b.
Proof.
  intros.
  induction b.
  - reflexivity.
  - simpl.
    destruct b.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - simpl.
    destruct b.
    + reflexivity.
    + rewrite IHb.
      rewrite plus_n_Sm.
      simpl. reflexivity.
    + rewrite IHb.
      rewrite plus_n_Sm.
      reflexivity.
Qed.


(* 
Fixpoint nat_to_bin (n: nat) : bin :=
  match n with
  | O => Z
  | S O => B1 Z
  | S  => 
             *)
