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
Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros.
  destruct H as [_ HQ].
  apply HQ.
Qed.

(* disjunction/logical or *)
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
