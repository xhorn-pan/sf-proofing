From LF Require Export Poly.

Theorem silly_ex : forall p,
    (forall n, even n = true -> even (S n) = false)
    -> (forall n, even n = false -> odd n = true)
    -> even p = true
    -> odd (S p) = true.
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Search rev.

Theorem rev_exercise1 : forall (l l': list nat), l = rev l' -> l' = rev l.
Proof.
  intros.
  symmetry.
  rewrite H.
  apply rev_involutive.
Qed.

Theorem trans_eq : forall (X: Type) (n m o: X), n = m -> m = o -> n = o.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  apply trans_eq with (m:=[c;d]).
  apply H.
  apply H0.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  transitivity [c;d].
  apply H.
  apply H0.
Qed.

(* should be in basic.v *)
Definition minustwo (n: nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
  
Example trans_eq_exercise: forall (n m o p: nat),
    m = (minustwo o) -> (n + p) = m ->
    (n+p) = (minustwo o).
Proof.
  intros.
  transitivity m.
  - apply H0.
  - apply H.
Qed.
  
(* Injecttion and discriminate *)
Theorem S_injective : forall (n m: nat), S n = S m -> n = m.
Proof.
  intros.
  assert (H2 : n = pred (S n)). { reflexivity. }
  rewrite H2.
  rewrite H.
  reflexivity.
Qed.

Theorem S_injective' : forall (n m: nat), S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.
  
Theorem injection_ex1 : forall (n m o : nat), [n; m] = [o; o] -> n = m.
Proof.
  intros.
  injection H as H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Example injection_ex2: forall (X: Type) (x y z: X) (l j : list X),
    x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros.
  rewrite H0 in H.
  injection H as H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

(* principle of explosion asserts that a contradictory hypothesis entails anything (even manifestly false things!) *)
Theorem discriminate_ex1 : forall (n m: nat), false = true -> n = m.
Proof.
  intros.
  discriminate H.
Qed.

Example discriminate_ex3: forall (X: Type) (x y z:X) (l j: list X),
    x :: y :: l = [] -> x = z.
Proof.
  intros.
  discriminate H.
Qed.

(* using tactics on hypothesises *)
Theorem S_inj : forall (n m: nat) (b: bool), ((S n) =? (S m)) = b -> (n =? m) = b.
Proof.
  intros.
  simpl in H.
  apply H.
Qed.

Theorem silly4 : forall (n m p q: nat), (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros.
  symmetry in H0.
  apply H in H0.
  symmetry in H0.
  apply H0.
Qed.
                
(*  specializing hypothesises *)
Theorem specialize_example: forall n, (forall m, m * n = 0) -> n = 0.
Proof.
  intros.
  specialize H with (m := 1).
  simpl in H.
  rewrite add_comm in H.
  simpl in H.
  apply H.
Qed.


Theorem trans_eq_example''' : forall (a b c d e f: nat), [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros.
  specialize trans_eq with (m:=[c;d]) as H1.
  apply H1.
  - apply H.
  - apply H0.
Qed.

Locate f_equal.

Theorem double_injective : forall n m, double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + f_equal.
      apply IHn'.
      simpl in eq.
      injection eq as goal.
      apply goal.
Qed.

Theorem eqb_true : forall n m, n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m eq.
    destruct  m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + f_equal.
      apply IHn'.
      simpl in eq.
      apply eq.
Qed.

Print plus_n_Sm.

Theorem plus_n_n_injective : forall n m, n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  induction m.
  - intros.
    reflexivity.
  - intros.
    inversion H.
  - intros.
    simpl in H.
    rewrite <- plus_n_Sm in H.
    destruct m.
    + inversion H.
    + f_equal.
      simpl in H.
      rewrite <- plus_n_Sm in H.
      injection H as goal.
      apply IHn' in goal.
      apply goal.
Qed.
      
Theorem plus_n_n_injective' : forall n m, n + n = m + m -> n = m.
Proof.
  intros n.
  induction n.
  - intros.
    destruct m.
    + reflexivity.
    + discriminate H.
  - intros.
    destruct m.
    + discriminate H.
    + f_equal.
      simpl in H.
      rewrite <- plus_n_Sm in H.
      injection H as goal.
      rewrite <- plus_n_Sm in goal.
      inversion goal.
      apply IHn in H0.
      apply H0.
Qed.
     
    
Theorem double_injective_take2 : forall n m, double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IHm'].
  - simpl.
    intros.
    destruct n.
    + reflexivity.
    + discriminate H.
  - intros.
    destruct n.
    + discriminate H.
    + f_equal.
      apply IHm'.
      injection H as goal.
      apply goal.
Qed.

Locate nth_error.

Theorem nth_error_after_last : forall (n: nat) (X: Type) (l: list X),
    length l = n -> OptionPlayground.nth_error l n = OptionPlayground.None.
Proof.
  intros.
  generalize dependent n.
  induction l.
  - simpl.
    destruct n.
    + intros.
      reflexivity.
    + intros.
      discriminate H.
  - destruct n.
    + intros.
      discriminate H.
    + intros.
      simpl in H.
      simpl.
      injection H as goal.
      apply IHl in goal.
      apply goal.
Qed.
      
(* unfolding definitions *)
Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  Abort.
