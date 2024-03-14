Check nat_ind.

Theorem mul_0_r' : forall n : nat, n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros. apply H.
Qed.

Theorem plus_one_r' : forall n:nat, n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. rewrite H. reflexivity.
Qed.

Inductive time : Type :=
| day
| night.
Check time_ind.

Inductive rgb : Type :=
| red
| green
| blue.

Check rgb_ind.

Inductive natlist : Type :=
| nnil
| ncons (n: nat) (l : natlist).

Check natlist_ind.

Inductive natlist' : Type :=
| nnil'
| nsnoc (l : natlist') (n : nat).

Check natlist'_ind.

(* Exercise booltree_ind *)
Inductive booltree : Type :=
| bt_empty
| bt_leaf (b : bool)
| bt_branch (b : bool) (t1 t2 : booltree).

Check booltree_ind.

Definition booltree_property_type : Type := booltree -> Prop.
Definition base_case (P : booltree_property_type) : Prop := P bt_empty.
Definition leaf_case (P : booltree_property_type) : Prop := forall b: bool, P (bt_leaf b).
Definition branch_case (P : booltree_property_type) : Prop := forall (b: bool)  (t1 : booltree), P t1 -> forall t2 : booltree, P t2 -> P (bt_branch b t1 t2).

Definition booltree_ind_type := forall (P : booltree_property_type),
    base_case P -> leaf_case P -> branch_case P -> forall (b : booltree), P b.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.
  exact booltree_ind.
Qed.

Inductive Toy : Type :=
| con1 (b : bool)
| con2 (n : nat) (t : Toy).

Theorem Toy_correct : exists f g, forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof.
  exists con1, con2.
  exact Toy_ind.
Qed.

(* Ploymorphism *)
Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Inductive tree (X : Type) : Type :=
| leaf (x : X)
| node (t1 t2 : tree X).

Check tree_ind.

Inductive mytype (X : Type) : Type :=
| constr1 (x : X)
| constr2 (n : nat)
| constr3 (m : mytype X) (n : nat).

Check mytype_ind.

Inductive foo (X Y : Type) : Type :=
| bar (x : X)
| baz (y : Y)
| quux : (nat -> foo X Y) -> nat -> foo X Y. (* ** *)

Check foo_ind.

Inductive foo' (X : Type) : Type :=
| C1 (l : list X) (f : foo' X)
| C2.

(* foo'_ind :
   forall (X : Type) (P : foo' X -> Prop),
       (forall (l : list X) (f: foo' X),
               P f -> P (C1 X l f)) ->
       P (C2 X) ->
       forall f1 : foo' X, P f1
*)
Check foo'_ind.

(* Induction Hypotheses *)
Definition P_m0r (n:nat) : Prop := n * 0 = 0.
Definition P_m0r' : nat -> Prop := fun n => n * 0 = 0.
Theorem mul_0_r'' : forall n:nat, P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros.
    unfold P_m0r in H.
    unfold P_m0r.
    simpl. apply H.
Qed.
(* The induction hypothesis is the premise of this latter implication
-- the assumption that P holds of n', which we are allowed to use in
proving that P holds for S n'. *)

(* More on the induction Tactic *)
(* add_comm' *)
Definition P_add_comm' (n m : nat) : Prop := n + m = m + n.
Theorem add_comm' : forall n m : nat, P_add_comm' n m.
Proof.
  intros n.
  apply nat_ind.
  - unfold P_add_comm'. rewrite <- plus_n_O. simpl. reflexivity.
  - intros.
    unfold P_add_comm' in H.
    unfold P_add_comm'.
    simpl. rewrite <- H.
    rewrite plus_n_Sm.
    reflexivity.
Qed.
(* add_assoc' *)
Definition P_add_assoc' (n m p : nat) : Prop := n + (m + p) = (n + m) + p.
Theorem add_assoc' : forall n m p : nat, P_add_assoc' n m p.
Proof.
  intros.
  apply nat_ind.
  - unfold P_add_assoc'. rewrite <- plus_n_O. rewrite <- plus_n_O. reflexivity.
  - intros.
    unfold P_add_assoc' in H.
    unfold P_add_assoc'.
    rewrite <- plus_n_Sm.
    rewrite <- plus_n_Sm.
    rewrite H.
    rewrite plus_n_Sm.
    reflexivity.
Qed.
