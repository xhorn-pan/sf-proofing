Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Theorem ev_4 : ev 4.
Proof.
  Show Proof.
  apply ev_SS. Show Proof.
  apply ev_SS. Show Proof.
  apply ev_0. Show Proof.
Qed.
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros h H. Show Proof.
  simpl. Show Proof.
  apply ev_SS. Show Proof.
  apply ev_SS. Show Proof.
  apply H. Show Proof.
Qed.

Theorem ev_8 : ev 8.
Proof.
  Show Proof.
  apply (ev_SS 6 (ev_SS 4 (ev_4))).
Qed.
Definition ev_8' : ev 8 := ev_SS 6 (ev_SS 4 (ev_4)).
(* Quantifiers, Implications, Functions *)
Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n:nat) => fun (H : ev n) => ev_SS (S (S n)) (ev_SS n H).
Definition ev_plus4'' (n:nat) (H:ev n) : ev (4+n) :=
  ev_SS (S (S n)) (ev_SS n H).
Definition ev_plus2 : Prop := forall n, forall (E: ev n), ev (n + 2).
Definition ev_plus2' : Prop := forall n, forall (_: ev n), ev (n + 2).
Definition ev_plus2'' : Prop := forall n, ev n -> ev (n + 2).
(* in general "P->Q" is just syntactic sugar for "forall (_:P), Q" *)


(* Logical Connectives as Inductive Types *)
Module Props.
  Module And.
    Inductive and (P Q : Prop) : Prop := | conj : P -> Q -> and P Q.
    Arguments conj [P] [Q].
    Notation "P /\ Q" := (and P Q) : type_scope.

    Print prod.
    Theorem proj1' : forall P Q, P /\ Q -> P.
    Proof.
      intros P Q [HP HQ]. apply HP.
      Show Proof.
    Qed.

    Lemma add_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
    Proof.
      intros P Q. split. Show Proof.
      - intros [HP HQ]. split. Show Proof.
        + apply HQ. Show Proof.
        + apply HP.
      - intros [HQ HP]. split. Show Proof.
        + apply HP.
        + apply HQ. Show Proof.
    Qed.
    Print conj.
  End And.
  Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
    match H with
    | conj HP HQ => conj HQ HP
    end.
  Print conj.
  Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
    conj (and_comm'_aux P Q) (and_comm'_aux Q P).
  Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
    fun (P Q R: Prop) (HPQ: P /\ Q) (HQR: Q /\ R) =>
      match HPQ, HQR with
      | conj hp hq, conj hq' hr => conj hp hr
      end.

  Module Or.
    Inductive or (P Q : Prop) : Prop :=
    | or_introl : P -> or P Q
    | or_intror : Q -> or P Q.

    Arguments or_introl [P] [Q].
    Arguments or_intror [P] [Q].

    Notation "P \/ Q" := (or P Q) : type_scope.
    Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
      fun P Q HP => or_introl HP.
    Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
    Proof. intros. left. apply H. Show Proof. Qed.

    Definition or_elim : forall (P Q R : Prop),
        (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
      fun P Q R HPQ HPR HQR =>
        match HPQ with
        | or_introl HP => HPR HP
        | or_intror HQ => HQR HQ
        end.

    Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
    Proof.
      intros P Q R HPQ HPR HQR.
      destruct HPQ as [HP | HQ].
      - apply (HPR HP).
      - apply (HQR HQ).
    Qed.
  End Or.
  Theorem or_commut'' : forall P Q, P \/ Q -> Q \/ P.
  Proof.
    intros P Q HPQ.
    destruct HPQ as [HP | HQ].
    - right. apply HP. Show Proof.
    - left. apply HQ. Show Proof.
  Qed.


  Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
    fun P Q HPQ =>
      match HPQ with
      | or_introl x => (fun HP => or_intror HP) x
      | or_intror x => (fun HQ => or_introl HQ) x
      end.
  Check or_commut''.

  Module Ex. (* need review *)
    Inductive ex {A :Type} (P : A -> Prop) : Prop := | ex_intro : forall x : A, P x -> ex P.
    Notation "'exists' x , p" := (ex (fun x => p))
                                   (at level 200, right associativity) : type_scope.
  End Ex.

  Check ex (fun n => ev (S n)) : Prop.
  Definition some_nat_is_even : exists n, ev n :=
    ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).
  Check (ex_intro).
  Check (ex_intro (fun x => ev x) 1).

  Theorem ex_ev_Sn' : ex (fun n => ev (S n)).
  Proof.
    exists 1. apply ev_SS. apply ev_0. Qed.

  Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
    ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

  (* True and False *)
  Inductive True : Prop := | I : True.

  Lemma p_implies_true' : forall P, P -> True.
  Proof.
    intros P H.
    apply I.
  Qed.

  Definition p_implies_true : forall P, P -> True :=
    fun P => fun P => I.

  (* False is an inductive type with no constructors,
     i.e. no way to build evidence for it *)
  Inductive False : Prop := .

  Definition false_implies_zero_eq_one : False -> 0 = 1 :=
    fun contra => match contra with end.

  Definition ex_falso_quodlibet' : forall P, False -> P :=
    fun P => fun contra => match contra with end.

  Module EqualityPlayground.
    Inductive eq {X:Type} : X -> X -> Prop := |eq_refl : forall x, eq x x.
    Notation "x == y" := (eq x y)
                           (at level 70, no associativity) : type_scope.
    Lemma four : 2 + 2 == 1 + 3.
    Proof. apply eq_refl. Qed.

    Definition four' : 2 + 2 == 1 + 3 := eq_refl 4.

    Definition singleton : forall (X : Type) (x : X), [] ++ [x] == x::[] :=
      fun (X:Type) (x:X) => eq_refl [x].

    Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
    fun n1 n2 Heq => match Heq with
                  | eq_refl n => eq_refl (S n)
                  end.

    Theorem eq_add' : forall (n1 n2: nat), n1 == n2 -> (S n1) == (S n2).
    Proof.
      intros n1 n2 Heq.
      Fail rewrite Heq.
      destruct Heq.
      Fail reflexivity.
      apply eq_refl.
    Qed.

    Lemma eq_cons' : forall (X:Type) (h1 h2: X) (t1 t2 : list X),
        h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2.
    Proof.
      intros.
      destruct H, H0.
      apply eq_refl.
    Qed.

    Definition eq_cons : forall (X:Type) (h1 h2 : X) (t1 t2 : list X),
        h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2 :=
      fun X h1 h2 t1 t2 Heqh Heqt =>
        match Heqh, Heqt with
        | eq_refl h, eq_refl t => eq_refl (h :: t)
        end.

    Lemma equality__leibniz_equality : forall (X:Type) (x y: X),
        x == y -> forall (P : X -> Prop), P x -> P y.
    Proof. intros. destruct H. apply H0. Qed.

    Definition equality__leibniz_equality_term : forall (X: Type) (x y: X),
        x == y -> forall P: (X -> Prop), P x -> P y :=
      fun X x y Heq => match Heq with
                    | eq_refl x => fun P => fun x => x
                    end.
    Lemma leibniz_equality__equality : forall (X : Type) (x y : X),
        (forall P: X->Prop, P x -> P y) -> x == y.
    Proof.
      intros X x y Hleibniz.
      apply Hleibniz. apply eq_refl.
    Qed.

  End EqualityPlayground.
End Props.
