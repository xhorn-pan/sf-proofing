From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Locate "+".
Print Init.Nat.add.

(* total maps *)
Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
                            (at level 100, right associativity).
Example example_empty := (_ !-> false).
Check example_empty.
Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, v at next level, right associativity).
Definition examplemap :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).
Print examplemap.

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof. intros. unfold t_empty. reflexivity. Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v; m) x = v.
Proof. intros.
       unfold t_update.
       rewrite String.eqb_refl.
       reflexivity.
Qed.

Lemma t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 -> (x1 !-> v; m) x2 = m x2.
Proof.
  intros. 
  unfold t_update.
  apply String.eqb_neq in H.
  destruct (String.eqb x1 x2) eqn:Ex.
  - discriminate H.
  - reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2; x !-> v1; m) = (x !-> v2 ; m).
Proof.
  intros.
  apply functional_extensionality.
  intros y.
  unfold t_update.
  destruct (String.eqb x y).
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x; m) = m.
Proof.
  intros.
  apply functional_extensionality.
  intros y.
  unfold t_update.
  destruct (String.eqb x y) eqn:Exy.
  - apply String.eqb_eq in Exy. rewrite Exy. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m: total_map A)
                             v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1; x2 !-> v2; m) = (x2 !-> v2; x1 !-> v1; m).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold t_update.
  destruct (String.eqb x1 x) eqn:Ex1.
  - destruct (String.eqb x2 x) eqn:Ex2.
    + destruct H.
      apply String.eqb_eq in Ex2.
      apply String.eqb_eq in Ex1.
      rewrite Ex2. 
      rewrite Ex1.
      reflexivity.
    + reflexivity.
  - destruct (String.eqb x2 x) eqn:Ex2.
    + reflexivity.
    + reflexivity.
Qed.

Definition paritial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : paritial_map A := t_empty None.
Definition update {A : Type} (m : paritial_map A)
  (x : string) (v : A) := (x !-> Some v; m).
Notation "x '|->' v ';' m" :=
  (update m x v)
    (at level 100, v at next level, right associativity).

Lemma apply_empty : forall (A : Type) (x : string), @empty A x = None.
Proof.
  intros. unfold empty.
  apply t_apply_empty.
Qed.

Lemma update_eq : forall (A : Type) (m : paritial_map A) x v,
    (x |-> v; m) x = Some v.
Proof.
  intros. unfold update.
  apply t_update_eq.
Qed.

(* update_eq lemma is used very often in proofs. adding it to coq's
   global "hint database" allows proof-automation tactics such as
   _auto_ to find it *)
#[global] Hint Resolve update_eq : core.
Theorem update_neq : forall (A:Type) (m:paritial_map A) x1 x2 v,
    x2 <> x1 -> (x2 |-> v; m) x1 = m x1.
Proof.
  intros. unfold update.
  apply t_update_neq. apply H.
Qed.

Lemma update_shadow : forall (A:Type) (m:paritial_map A) x v1 v2,
    (x |-> v2; x |-> v1; m) = (x |-> v2; m).
Proof.
  intros. unfold update.
  apply t_update_shadow.
Qed.

Lemma update_same : forall (A: Type) (m:paritial_map A) x v,
    m x = Some v -> (x |-> v; m) = m.
Proof.
  intros. unfold update.
  rewrite <- H.
  rewrite t_update_same.
  reflexivity.
Qed.
Lemma update_permute : forall (A:Type) (m:paritial_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1; x2 |-> v2; m) = (x2 |-> v2; x1 |-> v1; m).
Proof.
  intros. unfold update.
  apply t_update_permute.
  apply H.
Qed.

(* i don't get this *)
Definition includedin {A : Type} (m m' : paritial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : forall (A : Type) (m m' : paritial_map A)
                            (x : string) (vx : A),
    includedin m m' -> includedin (x |-> vx; m) (x |-> vx; m').
Proof.
  unfold includedin.
  intros A m m' x vx H y vy.
  destruct (eqb_spec x y).
  - rewrite e.
    rewrite update_eq.
    rewrite update_eq.
    intros H'. apply H'.
  - rewrite update_neq.
    + rewrite update_neq.
      { intros H'. apply H. apply H'. }
      apply n.
    + apply n.
Qed.
