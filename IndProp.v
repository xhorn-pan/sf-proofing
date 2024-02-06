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

Module Playground.
  Inductive le : nat -> nat -> Prop :=
  | le_n (n: nat) : le n n
  | le_S (n m : nat) (H: le n m) : le n (S m).

  Notation "n <= m" := (le n m).

  Theorem test_le1 : 3 <= 4.
  Proof. apply le_S. apply le_n. Qed.

  Theorem test_le3 : (2<=1) -> 2 + 2 = 5.
  Proof. intros. inversion H. inversion H2. Qed.

  Definition lt (n m : nat) := le (S n) m.
  Notation "n < m" := (lt n m).

End Playground.

Inductive total_relation : nat -> nat -> Prop := | tot_rel : forall n m, total_relation n m.
Inductive empty_relation : nat -> nat -> Prop := .

Theorem total_relation_is_total : forall n m, total_relation n m.
Proof. intros. apply tot_rel. Qed.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
Proof. unfold not. intros. inversion H. Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  induction 2.
  - apply H.
  - apply le_S. apply IHle. apply H.
Qed.

Theorem O_le_n : forall n, 0 <= n.
Proof.
  intros.
  induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m, n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m, S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply le_trans with (n := S n).
    + apply le_S. apply le_n.
    + apply H2.
Qed.

Theorem le_ge_cases : forall n m, (n < m) \/ (n >= m).
Proof.
  unfold "<".
  unfold ">=".
  intros n.
  induction n.
  - intros m.
    induction m.
    + right. auto.
    + left. destruct IHm.

Admitted.

Theorem le_plus_l : forall a b, a <= a + b.
Proof.
  intros.
  induction a.
  - simpl. apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.

Theorem plus_le : forall n1 n2 m, n1 + n2 <= m -> n1 <= m /\ n2 <= m.
Proof.
  intros.
  split.
  apply le_trans with (n := n1 + n2).
  apply le_plus_l. apply H.
  apply le_trans with (n := n1 + n2).
  rewrite add_comm. apply le_plus_l. apply H.
Qed.

Lemma le_Sn : forall n, n <= S n.
Proof. intros. apply le_S. apply le_n. Qed.

Theorem add_le_cases : forall n m p q,
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros.
  induction n.
  - left. apply O_le_n.
  - destruct m.
    + right. apply O_le_n.
    + destruct p.
      destruct q.
      * simpl in H.
        simpl in IHn.
        apply (le_trans (n + S m) (S (n + S m)) 0 (le_Sn (n + S m))) in H.
        apply IHn in H.
        left.
Admitted.

Theorem plus_le_compat_l : forall n m p, n <= m -> p + n <= p + m.
Proof.
  intros.
  induction H.
  - apply le_n with (n := p + n).
  - rewrite (add_comm p (S m)) .
    simpl.
    rewrite (add_comm p m) in IHle.
    apply (le_trans (p + n) (m + p) (S (m + p)) IHle (le_Sn (m+p))).
Qed.

Theorem plus_le_compat_r : forall n m p, n <= m -> n + p <= m + p.
Proof.
  intros.
  rewrite (add_comm n p).
  rewrite (add_comm m p).
  apply plus_le_compat_l.
  apply H.
Qed.

Theorem le_plus_trans : forall n m p, n <= m -> n <= m + p.
Proof.
  intros.
  induction p.
  - rewrite add_0_r. apply H.
  - rewrite (add_comm m p) in IHp.
    rewrite (add_comm m (S p)).
    simpl.
    apply (le_trans n (p+m) (S (p+m)) IHp (le_Sn (p+m))).
Qed.

Theorem n_le_m__n_le_m: forall n m, n < m -> n <= m.
Proof.
  intros.
  induction H.
  - apply le_Sn.
  - apply (le_trans _ _ _ IHle (le_Sn _)).
Qed.

Theorem plus_lt : forall n1 n2 m, n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  intros.
  split.
  - induction n2.
    + rewrite add_0_r in H. apply H.
    + apply IHn2.
      (* Search (_ < _).
      apply n_le_m__n_le_m in H.
      apply IHn2.
      apply n_le_m__n_le_m in IHn2.
      assert (Hs : n1 + n2 <= n1 + S n2).
      { apply plus_le_compat_l. apply le_Sn. }
      apply (le_trans (n1 + n2) (n1 + S n2) m Hs H).
       *)
Admitted.

Theorem leb_complete : forall n m, n <=? m = true -> n <= m.
Proof.
  intros.
  generalize dependent m.
  induction n as [|n' IHn'].
  - intros. apply O_le_n.
  - intros.
    destruct m.
    + discriminate.
    + simpl in H.
      apply n_le_m__Sn_le_Sm.
      apply IHn'.
      apply H.
Qed.

Theorem leb_correct : forall n m, n <= m -> n <=? m = true.
Proof.
  intros.
  generalize dependent n.
  induction m as [|m' IHm'].
  - intros.
    destruct n.
    + reflexivity.
    + inversion H.
  - intros.
    destruct n.
    + reflexivity.
    + simpl.
      apply Sn_le_Sm__n_le_m in H.
      apply IHm' in H.
      apply H.
Qed.

Theorem leb_iff : forall n m, n <=? m = true <-> n <= m.
Proof. split. apply leb_complete. apply leb_correct. Qed.

Theorem le_true_trans : forall n m o, n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  rewrite leb_iff.
  rewrite leb_iff in H.
  rewrite leb_iff in H0.
  apply (le_trans _ _ _ H H0).
Qed.
