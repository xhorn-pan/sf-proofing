Set Warnings "-notation-overridden,-parsing".
Set Warnings "-deprecated-hint-without-locality".
Require Nat.
From LF Require Export Tactics.

(* Coq is a typed language, Logical claims are no exception: any statement in Coq has a type, namely Prop.  *)

(* conjunction, or logical and, of propositions A and B is written A ^ B, it claims that both A and B are true. *)

Example and_example: 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise: forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  induction n.
  - simpl in H.
    apply conj.
    + reflexivity.
    + apply H.
  - simpl in H.
    discriminate H.
Qed.

Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros.
  destruct H as [HP _].
  apply HP.
Qed.


Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros.
  destruct H as [_ HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q: Prop, P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H.
  split.
  - apply H0.
  - apply H.
Qed.

(* disjunction/logical or *)
Lemma factor_is_O : forall n m: nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm.
    rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l: forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ: forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem mult_is_O : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  induction n.
  - left. reflexivity.
  - induction m.
    + right. reflexivity.
    + simpl in H.
      discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP|HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(* Falsehood and Negation *)
Definition not (P:Prop) := P -> False.
Check not : Prop -> Prop.
Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P: Prop), False -> P.
Proof.
  intros P.
  intros contra.
  destruct contra.
Qed.

Theorem not_implies_our_not : forall (P: Prop), ~P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  unfold not in H.
  destruct H.
  apply H0.
Qed.

Notation "x <> y" := (~(x = y)).
Theorem zero_not_one : 0 <> 1.
Proof. discriminate. Qed.

Theorem not_False : ~ False.
Proof.
  unfold not.
  intros.
  apply H. (* destruct H *)
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop, (P /\ ~ P) -> Q.
Proof.
  intros.
  unfold not in H.
  destruct H.
  destruct H0.
  apply H.
Qed.

Theorem double_neg : forall P : Prop, P -> ~~P.
Proof.
  intros.
  unfold not.
  intros.
  apply H0.
  apply H.
Qed.

Theorem contrapositive : forall (P Q: Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not.
  unfold not in H0.
  intros. (* was stuck here, TIL: when you have Prop1 -> Prop2, you need introduce Prop1 *)
  apply H0 in H.
  - apply H.
  - apply H1.
Qed.

Theorem not_both_true_and_false : forall P: Prop, ~ (P /\ ~ P).
Proof.
  intros.
  unfold not.
  intros.
  destruct H.
  apply H0.
  apply H.
Qed.

Theorem de_morgan_not_or : forall (P Q: Prop), not (P \/ Q) -> not P /\ not Q.
Proof.
  intros.
  unfold not.
  unfold not in H.
  apply conj.
  - intros.
    destruct H.
    apply or_intro_l.
    apply H0.
  - intros.
    destruct H.
    apply or_commut.
    apply or_intro_l.
    apply H0.
Qed.

Theorem not_true_is_false : forall b: bool, b <> true -> b = false.
Proof.
  intros.
  destruct b eqn:HE.
  - apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b: bool, b <> true -> b = false.
Proof.
  intros [] H.
  - exfalso.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

Theorem True_is_true : True.
Proof.
  apply I.
Qed.

Definition disc_fn (n: nat) : Prop :=
match n with
| O => True
| S _ => False
end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n H1. (* discriminate tactic takes care of all this *)
  assert (H2 : disc_fn 0). { simpl. apply I. }
  rewrite H1 in H2.
  simpl in H2.
  apply H2.
Qed.

Definition iif (P Q: Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" :=
  (iff P Q)
    (at level 95, no associativity)
    : type_scope.

Theorem iff_sym : forall P Q: Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros.
  destruct H.
  split.
  - apply H0.
  - apply H.
Qed.

Lemma not_true_iff_false : forall b, b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros.
    rewrite H.
    discriminate.
Qed.

Lemma apply_iff_example1 : forall P Q R: Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R.
  intros Hiff.
  intros H.
  intros HP.
  apply H.
  apply Hiff.
  apply HP.
Qed.

Lemma apply_iff_example2 : forall P Q R: Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Lemma apply_iff_example3 : forall P Q R: Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  destruct H.
  destruct H0.
  split.
  - intros.
    apply H in H3.
    apply H0 in H3.
    apply H3.
  - intros.
    apply H2 in H3.
    apply H1 in H3.
    apply H3.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros.
    destruct H.
    + split.
      ++ apply or_intro_l.
         apply H.
      ++ apply or_intro_l.
         apply H.
    + split.
      ++ apply proj1 in H.
         apply or_commut.
         apply or_intro_l.
         apply H.
      ++ apply proj2 in H.
         apply or_commut.
         apply or_intro_l.
         apply H.
  - intros [HPQ HPR].
    destruct HPQ.
    + apply or_intro_l.
      apply H.
    + destruct HPR.
      ++ apply or_intro_l.
         apply H0.
      ++ apply or_commut.
         apply or_intro_l.
         split.
         +++ apply H.
         +++ apply H0.
Qed.


(* setoids and logical equivalence *)
(* a setoid is a set equipped with a equivalence relation -- that is a relation that is reflexive, symmetric, and transitive *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Lemma or_assoc : forall P Q R: Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros.
  split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_eq_0_ternary : forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0.
  rewrite mul_eq_0.
  rewrite or_assoc.
  reflexivity.
Qed.

(* Existential Quantification *)
Definition Even x := exists n : nat, x = double n.

Theorem exists_example_2 : forall n, (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros.
  destruct H.
  exists (2 + x).
  apply H.
Qed.

Theorem dist_not_exists : forall (X: Type) (P: X -> Prop), (forall x, P x) -> ~(exists x, ~ P x).
Proof.
  unfold not.  (* ** *)
  intros.
  destruct H0.
  apply H0 in H.
  apply H.
Qed.

Theorem dist_exists_or : forall (X: Type) (P Q: X -> Prop), (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  - intros [x [EP | EQ]].
    + left.
      exists x. (* ** *)
      apply EP.
    + right.
      exists x.
      apply EQ.
  - intros.
    destruct H as [EP | EQ].
    + destruct EP.
      exists x.
      left.
      apply H.
    + destruct EQ.
      exists x.
      right.
      apply H.
Qed.


Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
  intros.
  generalize dependent m.
  induction n as [|n' IHn'].
  - intros.
    exists m.
    reflexivity.
  - intros m.
    destruct m.
    + intros H.
      discriminate H.
    + simpl.
      intros.
      apply IHn' in H.
      destruct H.
      exists x.
      f_equal.
      apply H.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros.
  generalize dependent m.
  induction n.
  - reflexivity.
  - intros.
    destruct m.
    + destruct H.
      discriminate H.
    + destruct H.
      simpl in H.
      apply S_injective in H.
      simpl.
      apply IHn.  (* ** *)
      exists x.
      apply H.
Qed.

(* Programming with propositions *)
Fixpoint In {A: Type} (x : A) (l: list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1;2;3;4;5].
Proof.
  simpl.
  right.
  right.
  right.
  left.
  reflexivity.
Qed.

Example In_example_2 : forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
 (* destruct H.
  - exists 1.
    rewrite <- H.
    reflexivity.
  - destruct H.
    + exists 2.
      rewrite <- H.
      reflexivity.
    + exfalso.
      apply H.
  *)
Qed.

(* ** *)
Theorem In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl.
    intros.
    apply H.
  - simpl.
    intros [H | H].
    + rewrite H.
      left.
      reflexivity.
    + right.
      apply IHl'.
      apply H.
Qed.


(* Theorem and_distributes_over_or : forall P Q R: Prop, P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  split.
  - intros [HP [HQ | HR]].
    + left.
      split.
      ++ apply HP.
      ++ apply HQ.
    + right.
      split.
      ++ apply HP.
      ++ apply HR.
  - intros.
    split.
    ++ destruct H.
       apply proj1 in H.
       apply H.
       apply proj1 in H.
       apply H.
    ++ destruct H.
       left.
       apply proj2 in H.
       apply H.
       right.
       apply proj2 in H.
       apply H.
Qed. *)

Theorem In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros.
  generalize dependent y.
  split.
  - induction l as [|x' l' IHl'].
    + simpl.
      intros.
      exfalso.
      apply H.
    + intros [H | H].
      ++ exists x'.
         split.
         +++ apply H.
         +++ left. reflexivity.
      ++ apply IHl' in H.
         destruct H.
         exists x.
         split.
         destruct H.
         +++ apply H.
         +++ simpl.
             right.
             destruct H.
             apply H0.
  - intros [x [F I]].
    rewrite <- F.
    apply In_map.
    apply I.

    (* induction l as [|x' l' IHl'].
    + intros H.
      destruct H.
      destruct H.
      simpl in H0.
      simpl.
      apply H0.
    + intros.
      simpl.
      simpl in H.
      destruct H.
      apply and_distributes_over_or in H.
      destruct H.
      ++ left.
         destruct H.
         rewrite <- H0 in H.
         apply H.
      ++ right.
         apply IHl'.
         exists x.
         apply H. *)
Qed.

Theorem In_app_iff : forall A l1 l2 (a:A), In a (l1 ++ l2) <-> In a l1 \/ In a l2.
Proof.
  split.
  - induction l1 as [|x1' l1' IHl1'].
    + simpl. intros.
      right.
      apply H.
    + induction l2 as [|x2' l2' IHl2'].
      ++ simpl.
         intros.
         destruct H as [H | H].
         +++ left. left.
             apply H.
         +++ apply IHl1' in H.
             apply or_assoc.
             right.
             apply H.
      ++ simpl.
         intros [H1 | H2].
         +++ left. left. apply H1.
         +++ apply IHl1' in H2.
             simpl in H2.
             destruct H2.
             { left. right. apply H.}
             { right. apply H.}
  - intros.
    induction l1 as [|x1' l1' IHl1'].
    + simpl. simpl in H.
      destruct H.
      ++ exfalso. apply H.
      ++ apply H.
    + simpl.
      simpl in H.
      destruct H as [[H|H]|H].
      ++ left. apply H.
      ++ right. apply IHl1'. left. apply H.
      ++ right. apply IHl1'. right. apply H.
Qed.

Fixpoint All  {T: Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ All P l'
  end.

Theorem All_In : forall T (P : T -> Prop) (l : list T), (forall x, In x l -> P x) <-> All P l.
Proof.
  intros. split.
  - induction l as [|h t].
    + reflexivity.
    + intros.
      simpl.
      split.
      ++ apply H. (* ** *)
         simpl.
         left.
         reflexivity.
      ++ apply IHt.
         intros.
         apply H.
         simpl.
         right.
         apply H0.
  - induction l.
    + intros. inversion H0.
    + intros.
      simpl in H0.
      simpl in H.
      destruct H.
      destruct H0.
      rewrite -> H0 in H.
      apply H.
      apply IHl.
      apply H1.
      apply H0.
Qed.

Definition conbine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if odd n then Podd n else Peven n.

Theorem conbine_odd_even_intro : forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) -> (odd n = false -> Peven n) -> conbine_odd_even Podd Peven n.
Proof.
  intros.
  unfold conbine_odd_even.
  destruct (odd n).
  - apply H. reflexivity.
  - apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd : forall (Podd Peven: nat -> Prop) (n : nat),
    conbine_odd_even Podd Peven n -> odd n = true -> Podd n.
Proof.
  intros.
  unfold conbine_odd_even in H.
  destruct (odd n).
  - apply H.
  - inversion H0.
Qed.


Theorem combine_odd_even_elim_even : forall (Podd Peven: nat -> Prop) (n : nat),
    conbine_odd_even Podd Peven n -> odd n = false -> Peven n.
Proof.
  intros.
  unfold conbine_odd_even in H.
  destruct (odd n).
  - inversion H0.
  - apply H.
Qed.

(* Applying Theorems to Arguments *)
Lemma add_comm3_take3 : forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros.
  rewrite add_comm.
  rewrite (add_comm z y).
  reflexivity.
Qed.

Theorem in_not_nil : forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
Admitted.
Check in_not_nil _ _ _.

Lemma in_not_nil_42_take5 : forall l : list nat, In 42 l -> l <> [].
Proof.
  intros.
  apply (in_not_nil _ _ _ H).
Qed.

Check In_map_iff _ _ _ _ _.

Example lemma_application_ex : forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mul_0_r in Hm.
  rewrite <- Hm.
  reflexivity.
Qed.


(* working with decidable properties *)
Lemma even_double : forall k, even (double k) = true.
Proof.
  intros.
  induction k.
  - reflexivity.
  - simpl. apply IHk.
Qed.

Lemma even_double_conv : forall n, exists k, n = if even n then double k else S (double k).
Proof.
  intros.
  induction n.
  - exists 0. reflexivity.
  - destruct IHn.
    destruct (even n) eqn:Hen.
    + rewrite -> even_S.
      rewrite -> Hen.
      simpl.
      rewrite -> H.
      exists x.
      reflexivity.
    + rewrite -> even_S.
      rewrite -> Hen.
      simpl.
      exists (S x).
      rewrite -> H.
      rewrite <- double_incr.
      reflexivity.
Qed.

Theorem even_bool_prop : forall n, even n = true <-> Even n.
Proof.
  split.
  - intros.
    destruct (even_double_conv n) as [k Hk].
    rewrite Hk.
    rewrite H.
    unfold Even.
    exists k.
    reflexivity.
  - intros.
    destruct H.
    rewrite H.
    apply even_double.
Qed.

Lemma eqb_eq : forall n m: nat, n =? m = true <-> n = m.
Proof.
  intros n m.
  split.
  - apply eqb_true.
  - intros. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Lemma plus_eqb_exx : forall n m p: nat, n =? m = true -> n + p =? m + p = true.
Proof.
  intros.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2: bool, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros.
  split.
  - intros.
    destruct b1.
    + destruct b2.
      ++ simpl in H.
         split.
         reflexivity.
         reflexivity.
      ++ simpl in H.
         split.
         reflexivity.
         inversion H.
    + simpl in H.
      inversion H.
  - intros [H1 H2].
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros.
  split.
  - intros.
    destruct b1.
    + left. reflexivity.
    + simpl in H. right. apply H.
  - intros [H1 | H2].
    + rewrite H1.
      reflexivity.
    + rewrite H2.
      destruct b1.
      * reflexivity.
      * reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat, x =? y = false <-> x <> y.
Proof.
  intros.
  rewrite <- eqb_eq. (* non sense. *)
  rewrite <- not_true_iff_false.
  reflexivity.
Qed.

Fixpoint eqb_list  {A : Type} (eqb: A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, [] => false
  | [], h2 :: t2 => false
  | h1 :: t1, h2 :: t2 => (eqb h1 h2) && eqb_list eqb t1 t2
  end.

Theorem eqb_list_true_iff : forall A (eqb: A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) -> forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1 as  [|h t IH].
  - destruct l2.
    + simpl. split.
      intros. reflexivity.
      intros. reflexivity.
    + simpl. split.
      intros. inversion H0.
      intros. inversion H0.
  - destruct l2.
    + simpl. split.
      intros. inversion H0.
      intros. inversion H0.
    + simpl. split.
      * intros.
        apply andb_true_iff in H0.
        destruct H0 as [H1 H2].
        apply H in H1.
        apply IH in H2.
        rewrite H1, H2.
        reflexivity.
      * intros.
        inversion H0.
        apply andb_true_iff.
        split.
        apply H. reflexivity.
        rewrite <- H3.
        apply IH. reflexivity.
Qed.

(* forallb *)
Theorem forallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros.
  split.
  - intros.
    induction l.
    + simpl. apply I.
    + simpl in H.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply IHl in H2.
      simpl.
      split.
      apply H1.
      apply H2.
  - intros.
    induction l.
    + reflexivity.
    + simpl.
      apply andb_true_iff.
      simpl in H.
      destruct H as [H1 H2].
      split.
      apply H1.
      apply IHl.
      apply H2.
Qed.

(* The Logic of Coq - Functional Extensionality *)
Axiom functional_extensionality : forall {X Y: Type} {f g: X -> Y},
    (forall (x: X), f x = g x) -> f = g.

Example function_equality_ex2 : (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x::l2)
  end.

Definition tr_rev {X} (l : list X) : list X := rev_append l []. (* tail-recursive *)

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  induction x as [|h x' IHx'].
  - reflexivity.
  - simpl.
    unfold tr_rev in IHx'.
    simpl in IHx'.
    simpl.
    rewrite <- IHx'.
    unfold tr_rev.
    destruct x'.
    + reflexivity.
    + simpl.
Abort.

(* classical vs contructive logic *)

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Theorem restricted_excluded_middle : forall P b, (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  left. rewrite H. reflexivity.
  right. unfold not. rewrite H. intros. discriminate H0.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat), n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

Theorem execuded_middle_irrefutable : forall (P : Prop), ~ ~ (P \/ ~ P).
Proof.
  intros P.
  unfold not.
  intros.
  apply H.
  right.
  intros.
  apply H.
  left.
  apply H0.
Qed.

Theorem not_exists_dist : excluded_middle -> forall (X: Type) (P: X -> Prop), ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros.
  assert (HP : P x \/ ~ P x). (* ** *)
  - apply H.
  - destruct HP.
    + apply H1.
    + unfold not in H0.
      destruct H0.
      exists x.
      apply H1.
Qed.
