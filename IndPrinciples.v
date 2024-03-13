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
