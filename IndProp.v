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

(* case study: Regular expressions *)
Inductive reg_exp (T : Type) : Type :=
| EmptySet
| EmptyStr
| Char (t: T)
| App(r1 r2 : reg_exp T)
| Union (r1 r2 : reg_exp T)
| Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : [] =~ EmptyStr
| MChar x : [x] =~ (Char x)
| MApp s1 re1 s2 re2
    (H1 : s1 =~ re1)
    (H2: s2 =~ re2)
  : (s1 ++ s2) =~ (App re1 re2)
| MUnionL s1 re1 re2 (H1 : s1 =~ re1)
  : s1 =~ (Union re1 re2)
| MUnionR re1 s2 re2 (H2 : s2 =~ re2)
  : s2 =~ (Union re1 re2)
| MStar0 re : [] =~ (Star re)
| MStarApp s1 s2 re
    (H1 : s1 =~ re)
    (H2 : s2 =~ (Star re))
  : (s1 ++ s2) =~ (Star re)
where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~([1; 2] =~ Char 1).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl.
  apply (MApp [1]).
  - apply MChar.
  - apply (MApp [2]).
    + apply MChar.
    + apply (MApp[3]).
      * apply MChar.
      * apply MEmpty.
Qed.

Lemma MStar1 : forall T s (re : reg_exp T), s =~ re -> s =~ Star re.
Proof.
  intros.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T), ~ (s =~ EmptySet).
Proof. unfold not. intros s t H. inversion H. Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
    s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros.
  destruct H.
  - apply (MUnionL _ _ _ H).
  - apply (MUnionR _ _ _ H).
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
    (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  - simpl. apply MStar0.
  - simpl.
    apply MStarApp.
    + apply H. left. reflexivity.
    + apply IHss.
      intros.
      apply H.
      right. apply H0.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
    s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros.
  induction H.
  - (* MEmpty *)
    simpl in H0. destruct H0.
  - (* MChar *)
    simpl in H0.
    simpl. apply H0.
  - (* MApp *)
    simpl.
    rewrite In_app_iff.
    rewrite In_app_iff in H0.
    destruct H0 as [H0 | H0].
    + left. apply IHexp_match1 in H0. apply H0.
    + right. apply (IHexp_match2 H0).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IHexp_match H0).
  - (* MUNionR *)
    simpl. rewrite In_app_iff.
    right. apply (IHexp_match H0).
  - (* MStar0 *)
    simpl. destruct H0.
  - (* MStarApp *)
    simpl. 
    rewrite In_app_iff in H0.
    destruct H0.
    + apply (IHexp_match1 H0).
    + apply (IHexp_match2 H0).
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => re_not_empty re1 && re_not_empty re2
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
    (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros.
    destruct H.
    induction H.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
    + simpl. rewrite IHexp_match. reflexivity.
    + simpl. rewrite IHexp_match.
      destruct (re_not_empty re1).
      * reflexivity.
      * reflexivity.
    + reflexivity.
    + reflexivity.
  - intros.
    induction re.
    + simpl in H. inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H.
      rewrite andb_true_iff in H.
      destruct H as [H1 H2].
      destruct (IHre1 H1).
      destruct (IHre2 H2).
      exists (x ++ x0).
      apply MApp; assumption.
    + simpl in H.
      rewrite orb_true_iff in H.
      destruct H as [H | H].
      * destruct (IHre1 H).
        exists x. apply MUnionL. apply H0.
      * destruct (IHre2 H).
        exists x. apply MUnionR. apply H0.
    + exists []. apply MStar0.
Qed.

Lemma star_app : forall T (s1 s2 : list T) (re : reg_exp T),
    s1 =~ Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H.
  remember (Star re) as re'.
  induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - intros. simpl. apply H.
  - intros. rewrite <- app_assoc.
    apply MStarApp.
    + apply H.
    + apply IHexp_match2.
      * apply Heqre'.
      * apply H1.
Qed.

Lemma MStar'' : forall T (s: list T) (re : reg_exp T),
    s =~ Star re ->
    exists ss : list (list T),
      s = fold app ss []
      /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros.
  remember (Star re) as re'.
  induction H as [|x' |s1 re1 s2 re2 Hm1 IH1 Hm2 IH2
                 |s1 re1 re2 Hm IH | re1 s2 re2 Hm IH
                  | re'' | s1 s2 re'' Hm1 IH1 Hm2 IH2].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split.
    + reflexivity.
    + intros. inversion H.
  - destruct (IH2 Heqre') as [ss' [L R]]. (* ** *)
    exists (s1::ss').
    split.
    + simpl. rewrite <- L. reflexivity.
    + intros.
      destruct H.
      * rewrite <- H. inversion Heqre'. rewrite H1 in Hm1. apply Hm1.
      * apply R. apply H.
Qed.

Module Pumping.

  Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
    match re with
    | EmptySet => 1
    | EmptyStr => 1
    | Char _ => 2
    | App re1 re2 => pumping_constant re1 + pumping_constant re2
    | Union re1 re2 => pumping_constant re1 + pumping_constant re2
    | Star r => pumping_constant r
    end.

  Lemma pumping_constant_ge_1 : forall T (re : reg_exp T), 1 <= pumping_constant re.
  Proof.
    intros.
    induction re.
    - apply le_n.
    - apply le_n.
    - simpl. apply le_S. apply le_n.
    - simpl.
      apply le_trans with (n := pumping_constant re1).
      apply IHre1. apply le_plus_l.
    - simpl.
      apply le_trans with (n := pumping_constant re1).
      apply IHre1. apply le_plus_l.
    - simpl. apply IHre.
  Qed.

  Lemma pumping_constant_0_false : forall T (re : reg_exp T),
      pumping_constant re = 0 -> False.
  Proof.
    intros T re H.
    assert (Hp1 : 1 <= pumping_constant re).
    { apply pumping_constant_ge_1. }
    rewrite H in Hp1.
    inversion Hp1.
  Qed.

  Fixpoint napp {T} (n : nat) (l : list T) : list T :=
    match n with
    | 0 => []
    | S n' => l ++ napp n' l
    end.

  Lemma napp_plus : forall T (n m : nat) (l : list T),
      napp (n + m) l = napp n l ++ napp m l.
  Proof.
    intros T n m l.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn.
      rewrite app_assoc.
      reflexivity.
  Qed.

  Lemma napp_star : forall T m s1 s2 (re : reg_exp T),
      s1 =~ re -> s2 =~ Star re -> napp m s1 ++ s2 =~ Star re.
  Proof.
    intros.
    induction m.
    - simpl. apply H0.
    - simpl.
      rewrite  <- app_assoc.
      (* apply MStar1 in H.
      apply (star_app _ _ _ _ H IHm). *)
      apply MStarApp.
      apply H. apply IHm.
  Qed.

  Lemma weak_pumping : forall T (re : reg_exp T) s,
      s =~ re ->
      pumping_constant re <= length s ->
      exists s1 s2 s3, s = s1 ++ s2 ++ s3 /\
                    s2 <> [] /\
                    forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof.
    intros T re s Hm.
    induction Hm
      as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
         | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    - simpl. intros contra. inversion contra.
    - simpl. intros contra.
      apply Sn_le_Sm__n_le_m in contra. inversion contra.
    - (* MApp *)
      simpl. intros H.
      rewrite app_length in H.
      destruct (add_le_cases _ _ _ _ H) as [Hl1 | Hl2].
      + destruct (IH1 Hl1) as [x1 [x2 [x3 [H0 [H1 H2]]]]].
        rewrite H0.
        exists x1, x2, (x3 ++ s2). (* ** *)
        split.  rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
        split. apply H1.
        intros m.
        rewrite app_assoc, app_assoc. apply MApp.
          * rewrite <- app_assoc. apply H2.
          * apply Hmatch2.
      + destruct (IH2 Hl2) as [x1 [x2 [x3 [H0 [H1 H2]]]]].
        rewrite H0.
        exists (s1 ++ x1), x2, x3.
        split. rewrite <- app_assoc. reflexivity.
        split. apply H1.
        intros m.
        rewrite <- app_assoc. apply MApp.
        apply Hmatch1. apply H2.
    - (* MUnionL *)
      simpl. intros H.
      (* apply plus_le in H.
      apply proj1 in H.
      apply IH in H.
       *)
      destruct (IH (proj1 _ _ (plus_le _ _ _ H)))
        as [x0 [x1 [x2 [H0 [H1 H2]]]]].
      exists x0, x1, x2.
      split. apply H0.
      split. apply H1.
      intros m.
      apply MUnionL. apply H2.
    - (* MUnionR *)
      simpl. intros H.
      destruct (IH (proj2 _ _ (plus_le _ _ _ H)))
        as [x0 [x1 [x2 [H0 [H1 H2]]]]].
      exists x0, x1, x2.
      split. apply H0.
      split. apply H1.
      intros m.
      apply MUnionR. apply H2.
    - (* MStar0 *)
      simpl. intros.
      inversion H.
      apply pumping_constant_0_false in H2.
      exfalso. apply H2.
    - (* MStarApp *)
      intros H.
      exists [], (s1 ++ s2), [].
      rewrite app_nil_r.
      split. reflexivity.
      split.
      {
        destruct (s1 ++ s2) eqn:Ess.
        + exfalso. simpl in H. inversion H.
          apply pumping_constant_0_false in H2. apply H2.
        + intros. discriminate.
      }
      {
        intros m.
        rewrite app_nil_r.
        simpl.
        induction m.
        - simpl. apply MStar0.
        - simpl. apply star_app.
          + apply (MStarApp _ _ _ Hmatch1 Hmatch2).
          + apply IHm.
      }
  Qed.

  Lemma pumping : forall T (re : reg_exp T) s,
      s =~ re ->
      pumping_constant re <= length s ->
      exists s1 s2 s3, s = s1 ++ s2 ++ s3 /\
                    s <> [] /\
                    length s1 + length s2 <= pumping_constant re /\
                    forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof.
    intros T re s Hmatch.
    induction Hmatch
      as [| x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
         | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    - (* MEmpty *)
      simpl. intros H. inversion H.
    - (* MCHar *)
      simpl. intros H. apply Sn_le_Sm__n_le_m in H. inversion H.
    - (* MApp *)
      simpl. intros H.
      rewrite app_length in H.
      destruct (add_le_cases _ _ _ _ H) as [Hl1 | Hl2].
      + destruct (IH1 Hl1) as [x1 [x2 [x3 [H0 [H1 [H2 H3]]]]]].
        exists x1, x2, (x3 ++ s2). (* ** *)
  Admitted.
End Pumping.

(* case study: Improving Reflection *)
Theorem filter_not_empty_In : forall n l,
    filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros. apply H. reflexivity.
  - simpl. destruct (n =? m) eqn:H.
    + intros. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + intros. right. apply IHl'. apply H0.
Qed.

Inductive reflect (P: Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H.
  destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. unfold not. rewrite H. discriminate.
Qed.

Theorem  reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros.
  inversion H.
  - split.
    + intros. reflexivity.
    + intros. apply H0.
  - unfold not in H0.
    split.
    + intros. exfalso. apply (H0 H2).
    + intros. discriminate H2.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
    filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l.
  induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (eqbP n m) as [H' | H'].
    + left. symmetry. apply H'.
    + right. apply IHl'. apply H.
Qed.

Fixpoint count n l :=
  match l with
  | []  => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
    count n l = 0 -> ~ (In n l).
Proof.
  intros n l Hcount.
  induction l as [| m l' IHl'].
  - unfold not. simpl. intros H. apply H.
  - simpl in Hcount.
    destruct (eqbP n m) as [H | H].
    + discriminate Hcount.
    + simpl in Hcount. apply IHl' in Hcount.
      unfold not in Hcount.
      unfold not in H.
      unfold not. simpl. intros [H'| H'].
      apply H. symmetry. apply H'.
      apply Hcount. apply H'.
Qed.
