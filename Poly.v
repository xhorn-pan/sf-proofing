From LF Require Export List.

(* polymorphic *)

Inductive list (X : Type) : Type :=
| nil
| cons (x : X) (l : list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat.

Check repeat'.

(*
  ^Coq able to use _type inference_ to deduce what the types of X x and count must be,
  based on how they are used.

  When Coq encounters a _ ("hole"), it will attempt to unify all locally available info,
  - the type of the function being applied
  - the types of the other arguments
  - the type expected by the context in which the application appears.
  to determine what concrete type should replace the _.

  We can declare an argument to be implicit when defining the function itself, by surrounding
  it in curly braces instead of parens.
 *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint repeat'' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat'' x count')
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (length t)
  end.

Example test_rev1 : rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2: rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Notation "x :: y" := (cons x y)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

(* Exercise *)
Theorem app_nil_r : forall (X : Type), forall l:list X,
    l ++ [] = l.
Proof.
  intros t l.
  induction l.
  - reflexivity.
  - simpl.
    rewrite -> IHl.
    reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    rewrite -> IHl.
    reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2: list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl.
    rewrite -> IHl1.
    reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  - simpl.
    rewrite -> app_nil_r.
    reflexivity.
  - simpl.
    rewrite -> IHl1.
    rewrite -> app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X, rev (rev l) = l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    rewrite -> rev_app_distr.
    rewrite -> IHl.
    reflexivity.
Qed.

(* Polymorphic Pairs *)
Inductive prod (X Y : Type) : Type := | pair (x : X) (y : Y).
Arguments pair {X} {Y}.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

(*
  type_scope tell Coq that the abbreviation should only be used when parsing types,
  not when parsing expressions
 *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.
      
Fixpoint conbine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (conbine tx ty)
  end.

Fixpoint  split {X Y : Type} (l : list (X*Y)): (list X) * (list Y) :=
  match l with
  | nil => ([] , [])
  | (x, y) :: l' => ( x :: fst (split l'), y :: snd (split l'))
  end.

Example test_split: split [(1,false); (2,false)] = ([1;2], [false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.
  Inductive option (X:Type) : Type := | Some (x : X) | None.
  Arguments Some {X}.
  Arguments None {X}.

  Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
             | O => Some a
             | S n' => nth_error l' n'
             end
  end.

  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.

  Definition hd_error {X : Type} (l : list X) : option X :=
    match l with
    | nil => None
    | h :: _ => Some h
    end.

  Example test_hd_error1: hd_error [1;2] = Some 1.
  Proof. reflexivity. Qed.
  Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
  Proof. reflexivity. Qed.
  
End OptionPlayground.

(* Functions as Data *)
(* high order functions *)
Definition doit3times {X : Type} (f : X -> X) (n:X) : X := f (f (f n)).
Check @doit3times.
(* : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times : doit3times negb true = false.
Proof. reflexivity. Qed.

(* Filter *)
Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
            else filter test t
  end.
Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_one {X : Type} (l : list X) : bool := (length l) =? 1.
Example test_filter2:
  filter length_is_one [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat := length (filter odd l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Locate "_ > _".

(* Anonymous Functions *)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => even n && (ltb 7 n)) l.
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  ((filter (fun n => test n) l), (filter (fun n => negb (test n)) l)).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* Map *)
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Lemma map_lists : forall (X Y : Type) (f: X -> Y) (l1 l2 : list X),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl.
    rewrite ->  IHl1.
    reflexivity.
Qed.
 
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros.
  simpl.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite <- IHl'.
    apply map_lists.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.


(* Fold *)
Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

(* Functions That Construct Functions *)
Definition constfun {X: Type} (x: X) : nat -> X := fun (k:nat) => x.
Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Module  Exercises.
  Definition fold_length {X:Type} (l: list X) : nat :=
    fold (fun _ n => S n) l 0.
  Example test_fold_length1: fold_length [4;7;0] = 3.
  Proof. reflexivity. Qed.

  Theorem fold_length_correct : forall X (l: list X),
      fold_length l = length l.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - simpl.
      rewrite <- IHl.
      reflexivity.
  Qed.

  Definition fold_map {X Y: Type} (f: X->Y) (l: list X) : list Y := fold (fun n l' => (f n) :: l') l nil.
  
  Example test_fold_map: fold_map odd [2;1;2;5] = [false;true;false;true].
  Proof. reflexivity. Qed.

  Theorem fold_map_correct : forall {X Y:Type} (f: X -> Y) (l: list X),
      map f l = fold_map f l.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - simpl.
      rewrite -> IHl.
      reflexivity.
  Qed.


(*
 * Currying
   converting from X * Y -> Z to X -> Y -> Z is called currying.
                   X-> Y -> Z to X * Y -> Z            uncurrying.
 *)
  Definition prod_curry {X Y Z: Type} (f: X * Y -> Z) (x: X) (y: Y) : Z := f (x, y).
  Definition prod_uncurry {X Y Z: Type} (f: X -> Y -> Z) (p: X * Y) : Z := f (fst p) (snd p).

  Check @prod_curry.
  Check @prod_uncurry.

  Theorem uncurry_curry : forall (X Y Z: Type) (f: X -> Y -> Z) x y,
      prod_curry (prod_uncurry f) x y = f x y.
  Proof. reflexivity. Qed.

  Theorem curry_uncarry : forall (X Y Z: Type) (f: (X * Y) -> Z) (p: X * Y),
      prod_uncurry (prod_curry f) p = f p.
  Proof.
    intros.
    destruct p.
    reflexivity.
  Qed.

  (* nth_error_informal *)
  Fixpoint nth_error  {X : Type} (l: list X) (n: nat) : option X :=
    match l with
    | [] => None
    | a :: l' => if n =? 0 then Some a else nth_error l' (pred n)
    end.
  
  (* definition of nth_error *)
  Theorem list_nth_none : forall {X: Type} (lst: list X) (len: nat),
      length lst = len -> @nth_error X lst len = None.
  Proof.
    intros.
    induction lst.
    - reflexivity.
    - rewrite <- H.
      simpl.
  Abort.
     
(*
  Theorem: forall X l n, length l = n -> @nth_error X l n = None
  Proof.
    by induction on l.
    - first, suppose l = [], then n = 0, nth_error X l 0 = None,
    which follows directly from the definition of nth_error.

    - next, suppose l = h :: l', with
      length l' = len -> @nth_error X l' len = None.
      we mush show
      length (h::l') = S len -> @nth_error X (h :: l') (S len) = None.


      how to prove/connect/apply the definition of length?
   *)

    Module Church.
      Definition cnat := forall X: Type, (X -> X) -> X -> X.
      Definition zero: cnat := fun (X: Type) (f: X->X)(x:X) => x.
      Definition one: cnat := fun (X: Type) (f: X->X) (x:X) => f x.
      Definition two: cnat := fun (X: Type) (f: X->X) (x:X) => f (f x).

      Definition zero': cnat := fun (X: Type) (succ: X->X) (zero:X) => zero.
      Definition one': cnat := fun (X: Type) (succ: X->X) (zero:X) => succ zero.
      Definition two': cnat := fun (X: Type) (succ: X->X) (zero:X) => succ (succ zero).

      Example zero_church_peano : zero nat S O = 0.
      Proof. reflexivity. Qed.
      Example one_church_peano : one nat S O = 1.
      Proof. reflexivity. Qed.
      Example two_church_peano : two nat S O = 2.
      Proof. reflexivity. Qed.

      (* Exercise church_scc/plus/mult *)
      Definition scc (n: cnat) : cnat := fun (X: Type) (f: X->X) (x:X) => f (n X f x).
      
      Definition plus (n m: cnat) : cnat := fun (X: Type) (f: X->X) (x:X) => n X f (m X f x).
      Compute (plus).
      
      Example plus_2 : plus two one = plus one two.
      Proof. reflexivity. Qed.

      Definition mult (n m: cnat) : cnat := fun (X: Type) (f: X->X) (x:X) => (n X (m X f) x).
      Compute (mult).
      
      Example mult_1 : mult one one = one.
      Proof. reflexivity. Qed.

      Example mult_2 : mult zero (plus one one) = zero.
      Proof. reflexivity. Qed.

      Definition exp (n m: cnat) : cnat := fun (X: Type) (f: X->X) (x:X) => (m (X -> X) (n X) f x).

      Compute (exp one).
      Example exp_2 : exp two zero = one.
      Proof. reflexivity. Qed.
    End Church.
End Exercises.

