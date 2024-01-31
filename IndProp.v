Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.

Inductive le : nat -> nat -> Prop :=
| le_n (n : nat) : le n n
| le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

Inductive clos_trans {X: Type} (R: X -> X -> Prop) : X -> X -> Prop :=
| t_step (x y: X) : R x y -> clos_trans R x y
| t_trans (x y z : X) : clos_trans R x y -> clos_trans R y z -> clos_trans R x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.
Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_SM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop := clos_trans parent_of.
Example ancestor_of1: ancestor_of Sage Moss.
Proof.
  unfold ancestor_of.
  apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_SM.
Qed.

Inductive clos_refl_trans {X : Type} (RT: X -> X -> Prop) : X -> X -> Prop :=
| rt_refl (x y : X) : RT x y -> clos_refl_trans RT y x
| rt_trans (x y z : X) : clos_refl_trans RT x y -> clos_refl_trans RT y z -> clos_refl_trans RT x z. 

(* example: Permutations *)
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
| perm3_swap12 (a b c : X) : Perm3 [a;b;c] [b;a;c]
| perm3_swap23 (a b c : X) : Perm3 [a;b;c] [a;c;b]
| perm3_trans (l1 l2 l3 : list X) : Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Example Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap23.
Qed.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros. simpl.
  apply ev_SS. apply ev_SS.
  apply H.
Qed.

Theorem ev_double : forall n, ev (double n).
Proof.
  intros.
  induction n.
  - simpl. apply ev_0.
  - simpl.
    apply ev_SS.
    apply IHn.
Qed.

(* using evidence in proofs *)
Theorem ev_inversion : forall (n : nat), ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros.
  destruct H as [|n' IHn'] eqn:HE.
  - left. reflexivity.
  - right.
    exists n'.
    split.
    + reflexivity.
    + apply IHn'.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros.
  apply ev_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H as [n' [H0 H1]].
    injection H0 as Heq. rewrite Heq. apply H1.
Qed.

Theorem evSS_ev' : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H.
  inversion H as [|n' H' Heq].
  apply H'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  unfold not.
  intros.
  apply ev_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H as [m [H _]].
    discriminate H.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev_even : forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  apply evSS_ev in H.
  apply evSS_ev in H.
  apply H.
Qed.

Theorem SSSSev_even' : forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [|n' H1].
  inversion H1 as [|n'' H2].
  apply H2.
Qed.

Theorem ev5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  apply SSSSev_even in H.
  inversion H.
Qed.

Lemma ev_Even : forall n, ev n -> Even n.
Proof.
  intros.
  induction H.
  - unfold Even.
    exists 0.
    reflexivity.
  - unfold Even in IHev.
    destruct IHev.
    rewrite H0.
    unfold Even.
    exists (S x).
    simpl.
    reflexivity.
Qed.

Theorem ev_Even_iff : forall n, ev n <-> Even n.
Proof.
  intros n. split.
  - apply ev_Even.
  - unfold Even.
    intros [k Hk].
    rewrite Hk.
    apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [|n' Hn' IHn'].
  - simpl. apply Hm.
  - induction Hm as [|m' Hm' IHm'].
    + simpl.
      rewrite add_0_r.
      apply ev_SS.
      apply Hn'.
    + simpl.
      apply ev_SS.
      apply IHn'.
Qed.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  split.
  - intros H.
    induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply (ev_sum n m IHev'1 IHev'2).
  - intros H.
    induction H as [|n' Hn' IHn'].
    + apply ev'_0.
    + rewrite <- PeanoNat.Nat.add_1_r.
      rewrite <- PeanoNat.Nat.add_1_r.
      rewrite <- PeanoNat.Nat.add_assoc.
      simpl.
      apply (ev'_sum n' 2).
      apply IHn'.
      apply ev'_2.
Qed.

Theorem ev_ev___ev : forall n m, ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Hmn Hn.
  induction Hn.
  - rewrite add_comm in Hmn.
    rewrite add_0_r in Hmn.
    apply Hmn.
  - apply IHHn.
    simpl in Hmn.
    inversion Hmn.
    apply H0.
Qed.

Theorem ev_plus_plus : forall n m p, ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  apply ev_ev___ev with (n:=(n+n)) (m:=(m+p)).
  assert (H : ev (n + m) -> ev (n + p) -> ev ((n + m) + (n + p))).
  { intros. apply (ev_sum (n+m) (n+p) Hnm Hnp). }
  apply H in Hnm.
  rewrite PeanoNat.Nat.add_shuffle1 in Hnm.
  apply Hnm.
  apply Hnp.
  rewrite <- double_plus.
  apply ev_double.
Qed.
