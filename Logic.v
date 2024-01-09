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

Theorem In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros.
  split.
  - induction l as [|x' l' IHl'].
    + simpl.
      intros.
      exfalso.
      apply H.
    + simpl.
      intros.
      destruct H.
      ++
Abort.
    
