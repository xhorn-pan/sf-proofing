Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locallity".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.
Set Default Goal Selector "!".

Module AExp.
  
  Inductive aexp : Type  :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2: aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

  Fixpoint aeval (a : aexp) : nat  :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Example test_aeval1 : aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof. reflexivity. Qed.

  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => (aeval a1) =? (aeval a2)
    | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
    | BLe a1 a2 => (aeval a1) <=? (aeval a2)
    | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with
    | ANum n  => ANum n
    | APlus (ANum 0) e2 => optimize_0plus e2
    | APlus e1 e2  => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Theorem optimize_0plus_sound' : forall a, aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a.
    induction a;
      try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    - reflexivity.
    - destruct a1 eqn:Ea1;
        try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
      + destruct n eqn:En; simpl; rewrite IHa2; reflexivity.
  Qed.

  Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BNeq a1 a2 => BNeq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
    | BNot b => BNot (optimize_0plus_b b)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

  Theorem optimize_0plus_b_sound : forall b, beval (optimize_0plus_b b) = beval b.
  Proof.
    intros b.
    induction b;
      try (simpl; reflexivity);
      try (simpl; repeat rewrite optimize_0plus_sound'; reflexivity).
    - simpl. rewrite IHb. reflexivity.
    - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
  Qed.

  
End AExp.

Definition state := total_map nat.
Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BNeq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BGt (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                         (in custom com at level 0, only parsing,
                             f constr at level 0, x constr at level 9,
                             y constr at level 9) : com_scope.

Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~ (X <= 4) }>.
Fixpoint aeval (st: state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1) 
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Print empty_st.
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).
Example aexp1 : aeval (X !-> 5) <{ 3 + (X * 2) }> = 13.
Proof. reflexivity. Qed.
Example aexp2 : aeval (X !-> 5; Y !-> 4) <{ Z + (X * Y) }> = 20.
Proof. reflexivity. Qed.
Example bexp1 : beval (X !-> 5) <{ true && ~ (X <= 4) }> = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

Notation "'skip'" := CSkip (in custom com).
Notation "x '::=' a" := (CAsgn x a) (in custom com at level 100).
Notation "c1 ; c2" := (CSeq c1 c2) (in custom com at level 100, right associativity).
Notation "'while' b 'do' c 'end'" := (CWhile b c) (in custom com at level 100, right associativity).
Notation "'if' b 'then' c1 'else' c2 'fi'" := (CIf b c1 c2) (in custom com at level 100, right associativity).
                                   
Definition fact_in_coq : com := <{
      Z ::= X;
      Y ::= 1;
      while Z <> 0 do
                    Y ::= Y * Z;
                    Z ::= Z - 1
                    end }>. 
Unset Printing Notaions.
Print fact_in_coq.
Set Printing Notations.
Print fact_in_coq.
Locate ";".

Definition plus2 : com := <{ X ::= X + 2 }>.
Definition XtimesYinZ : com := <{ Z ::= X * Y }>.

Definition substract_slowly_body : com :=
  <{ Z ::= Z - 1; X ::= X - 1 }>.

Definition substract_slowly : com :=
  <{ while X <> 0 do
                   substract_slowly_body
                   end }>.
Definition substract_3_from_5_slowly : com :=
<{ X ::= 3 ; Z ::= 5; substract_slowly }>.


Definition loop : com :=
  <{ while true do
         skip
         end }>.
