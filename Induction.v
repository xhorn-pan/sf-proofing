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
