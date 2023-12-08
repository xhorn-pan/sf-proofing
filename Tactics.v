From LF Require Export Poly.

Theorem silly_ex : forall p,
    (forall n, even n = true -> even (S n) = false)
    -> (forall n, even n = false -> odd n = true)
    -> even p = true
    -> odd (S p) = true.
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Search rev.

Theorem rev_exercise1 : forall (l l': list nat), l = rev l' -> l' = rev l.
Proof.
  intros.
  symmetry.
  rewrite H.
  apply rev_involutive.
Qed.

Theorem trans_eq : forall (X: Type) (n m o: X), n = m -> m = o -> n = o.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  apply trans_eq with (m:=[c;d]).
  apply H.
  apply H0.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  transitivity [c;d].
  apply H.
  apply H0.
Qed.

(* should be in basic.v *)
Definition minustwo (n: nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
  
Example trans_eq_exercise: forall (n m o p: nat),
    m = (minustwo o) -> (n + p) = m ->
    (n+p) = (minustwo o).
Proof.
  intros.
  transitivity m.
  - apply H0.
  - apply H.
Qed.
  
(* Injecttion and discriminate *)
Theorem S_injective : forall (n m: nat), S n = S m -> n = m.
Proof.
  intros.
  assert (H2 : n = pred (S n)). { reflexivity. }
  rewrite H2.
  rewrite H.
  reflexivity.
Qed.

Theorem S_injective' : forall (n m: nat), S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.
  
Theorem injection_ex1 : forall (n m o : nat), [n; m] = [o; o] -> n = m.
Proof.
  intros.
  injection H as H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Example injection_ex2: forall (X: Type) (x y z: X) (l j : list X),
    x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros.
  rewrite H0 in H.
  injection H as H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

(* principle of explosion asserts that a contradictory hypothesis entails anything (even manifestly false things!) *)
Theorem discriminate_ex1 : forall (n m: nat), false = true -> n = m.
Proof.
  intros.
  discriminate H.
Qed.

Example discriminate_ex3: forall (X: Type) (x y z:X) (l j: list X),
    x :: y :: l = [] -> x = z.
Proof.
  intros.
  discriminate H.
Qed.

(* using tactics on hypothesises *)
Theorem S_inj : forall (n m: nat) (b: bool), ((S n) =? (S m)) = b -> (n =? m) = b.
Proof.
  intros.
  simpl in H.
  apply H.
Qed.

Theorem silly4 : forall (n m p q: nat), (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros.
  symmetry in H0.
  apply H in H0.
  symmetry in H0.
  apply H0.
Qed.
                
(*  specializing hypothesises *)
Theorem specialize_example: forall n, (forall m, m * n = 0) -> n = 0.
Proof.
  intros.
  specialize H with (m := 1).
  simpl in H.
  rewrite add_comm in H.
  simpl in H.
  apply H.
Qed.


Theorem trans_eq_example''' : forall (a b c d e f: nat), [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros.
  specialize trans_eq with (m:=[c;d]) as H1.
  apply H1.
  - apply H.
  - apply H0.
Qed.

Locate f_equal.

Theorem double_injective : forall n m, double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + f_equal.
      apply IHn'.
      simpl in eq.
      injection eq as goal.
      apply goal.
Qed.

Theorem eqb_true : forall n m, n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m eq.
    destruct  m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + f_equal.
      apply IHn'.
      simpl in eq.
      apply eq.
Qed.

Print plus_n_Sm.

Theorem plus_n_n_injective : forall n m, n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  induction m.
  - intros.
    reflexivity.
  - intros.
    inversion H.
  - intros.
    simpl in H.
    rewrite <- plus_n_Sm in H.
    destruct m.
    + inversion H.
    + f_equal.
      simpl in H.
      rewrite <- plus_n_Sm in H.
      injection H as goal.
      apply IHn' in goal.
      apply goal.
Qed.
      
Theorem plus_n_n_injective' : forall n m, n + n = m + m -> n = m.
Proof.
  intros n.
  induction n.
  - intros.
    destruct m.
    + reflexivity.
    + discriminate H.
  - intros.
    destruct m.
    + discriminate H.
    + f_equal.
      simpl in H.
      rewrite <- plus_n_Sm in H.
      injection H as goal.
      rewrite <- plus_n_Sm in goal.
      inversion goal.
      apply IHn in H0.
      apply H0.
Qed.
     
    
Theorem double_injective_take2 : forall n m, double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IHm'].
  - simpl.
    intros.
    destruct n.
    + reflexivity.
    + discriminate H.
  - intros.
    destruct n.
    + discriminate H.
    + f_equal.
      apply IHm'.
      injection H as goal.
      apply goal.
Qed.

Locate nth_error.

Theorem nth_error_after_last : forall (n: nat) (X: Type) (l: list X),
    length l = n -> OptionPlayground.nth_error l n = OptionPlayground.None.
Proof.
  intros.
  generalize dependent n.
  induction l.
  - simpl.
    destruct n.
    + intros.
      reflexivity.
    + intros.
      discriminate H.
  - destruct n.
    + intros.
      discriminate H.
    + intros.
      simpl in H.
      simpl.
      injection H as goal.
      apply IHl in goal.
      apply goal.
Qed.
      
(* unfolding definitions *)
Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1: forall m, foo m + 1 = foo (m + 1) + 1.
Proof. intros. simpl. reflexivity. Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_failed: forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros.
  simpl. (* Does nothing *)
Abort.

  
Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

(* using destruct on compound expressions *)
Definition sillyfun (n: nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
       else false.

Theorem sillyfun_false : forall (n: nat), sillyfun n = false.
Proof.
  intros.
  unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn:E2.
    + reflexivity.
    + reflexivity.
Qed.

(* exercise combine_split *)
Fixpoint split {X Y:Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t => match split t with
                 | (lx, ly) => (x :: lx, y :: ly)
                 end
  end. 

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2, split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros.
  induction l as [| (x, y) l'].
  - intros.
    inversion H.
    reflexivity.
  - intros.
    generalize dependent l2.
    generalize dependent l1.
    destruct (split l') eqn:E.
    + simpl.
Abort.


(* eqn: qualifier can carry important information to prove the goal *)
Theorem bool_fn_applied_thrice : forall (f: bool -> bool) (b:bool), f (f (f b)) = f b.
Proof.
  intros.
  destruct b.
  - destruct (f true) eqn:Eftrue.
    + rewrite Eftrue. apply Eftrue.
    + destruct (f false) eqn:Effalse.
      ++ apply Eftrue.
      ++ apply Effalse.
  - destruct (f false) eqn:Effalse.
    + destruct (f true) eqn:Eftrue.
      ++ apply Eftrue.
      ++ apply Effalse.
    + rewrite Effalse. apply Effalse.
Qed.

(* Review
  intros: move hypothesises/variables from goal to context.
  reflexivity: finish the proof(when the goal looks like e=e)
  apply: prove goal using a hypothesis, lemma, or contructor
  apply ... in H: apply a hypothesis, lemma, or contructor to a hypothesis in the context (forward reasoning)
  apply ... with ... : explicity specify values for variables that cannot be determined by pattern matching
  simpl: simplify computations in the goal.
  simpl in H. simplify computations in a hypothesis.
  rewrite: use an equality hypothesis (or lemma) to rewrite the goal.
  rewrite ... in H: ... or a hypothesis.
  symmetry: changes a goal of the form t = u into u = t.
  symmetry in H. changes a hypothesis of form t = u into u = t.
  transitivity y: prove a goal x = z by proving two new subgoals, x = y and y = z.
  unfold: replace a defined constant by its right-hand side in the goal.
  unfold ... in H: ... or a hypothesis.
  destruct ... as ...: case analysis on values of inductively defined types.
  destruct ... eqn:... : specify the name of an equation to be added to the context, recording the result of the case analysis.
  induction ... as ...: induction on values of inductively defined types.
  injection ... as ...: reason by injectivity on equalitues between values of inductively defined types.
  discriminate: reason by disjointness of contructors on equalitues between values of inductively defined types.
  assert (H:e) (or assert (e) as H): introduce a 'local lemma' e and call it H.
  generalize dependent x: move the variable x (and anything else that depends on it) from the context back to a explicit hypothesis in the goal formula.
  f_equal: change a goal of the form f x = f y into x = y.
*)

Check eqb_true.

Theorem eqb_sym : forall (n m: nat), (n =? m) = (m =? n).
Proof.
  intros.
  generalize dependent m.
  induction n.
  - intros.
    destruct m.
    + reflexivity.
    + reflexivity.
  - intros.
    induction m.
    + reflexivity.
    + simpl.
      apply IHn.
Qed.

Theorem eqb_trans: forall n m p, n =? m = true -> m =? p = true -> n =? p = true.
Proof.
  intros.
  apply eqb_true in H.
  apply eqb_true in H0.
  rewrite H.
  rewrite H0.
  apply eqb_refl.
Qed.

(* exercise split_combine *)
Definition split_combine_statement : Prop
  (* (": Prop" means that we are giving a name to a
     logical proposition here.) *)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.

Print filter.

(* exercise filter_exercise *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros.
  destruct l.
  - discriminate.
  - destruct (test x).
    + reflexivity.
    + generalize dependent x.
      intros.
      inversion H.
      
Abort.

(* forall_exists_challenge *)
Fixpoint forallb {X : Type} (f : X -> bool) (l : list X) : bool :=
    match l with
    | [] => true
    | x :: l' => f x && forallb f l'
    end.

Fixpoint existsb {X: Type} (f : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | x :: l' => f x || existsb f l'
  end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (f : X -> bool) (l : list X) : bool := negb (forallb negb (map f l)).

Example test_existsb'_1 : existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb'_2 : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb'_3 : existsb' odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb'_4 : existsb' even [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existb' : forall (X:Type) (f: X-> bool) (l: list X),
    existsb f l = existsb' f l.
Proof.
  intros.
  induction l.
  - unfold existsb'.
    simpl.
    reflexivity.
  - simpl.
    rewrite -> IHl.
    unfold existsb'.
    destruct (map f (x :: l)) eqn:Efx.
Abort.
