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
