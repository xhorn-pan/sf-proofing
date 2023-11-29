From LF Require Export Induction.

Module NatList.
  Inductive natprod : Type :=
  | pair (n1 n2 : nat).

  Check (pair 3 5) : natprod.
  
  Definition fst (p : natprod) : nat :=
    match p with
    | pair x t => x
    end.
  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y  => y
    end.

  Notation "( x , y )" := (pair x y).

  Compute (fst (3, 5)).

  Definition fst' (p : natprod) : nat :=
  match p with
  | (x, y) => x
  end.

  Definition snd' (p : natprod) : nat :=
  match p with
  | (x, y) => y
  end.

  Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

  (* Exercise *)
  Theorem snd_fst_is_swap : forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof.
    intros p.
    destruct p as [n m].
    simpl.
    reflexivity.
  Qed.
    
  Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

  Fixpoint  length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y) (right associativity, at level 60).

  Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

  (* Exercise *)
  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => if h =? 0 then nonzeros t else h :: nonzeros t
    end.
  Example test_nonzeros : nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.

  Fixpoint oddmembers (l: natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if odd h then h :: oddmembers t else oddmembers t
  end.
  
  Example test_oddmembers : oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.

  Definition countoddmembers (l : natlist) : nat := length (oddmembers l).
  
  Example test_countoddmembers1 : countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.

  Example test_countoddmembers2 : countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed. 

  Example test_countoddmembers3 : countoddmembers nil = 0.
  Proof. reflexivity. Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
    | nil, nil => nil
    | nil, l2 => l2
    | l1, nil => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
    end.

  Example test_alternate1 : alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.
  
  Example test_alternate2 : alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.

  Example test_alternate3 : alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.

  Example test_alternate4 : alternate [] [40;60] = [40;60].
  Proof. reflexivity. Qed.

  (* bag *)
  Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => 0
    | h :: t => if h =? v then 1 + count v t else count v t
    end.

  Example test_count1 : count 1 [1;2;3;1;4;1] = 3.
  Proof. reflexivity. Qed.

  Example test_count2 : count 7 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.
  
  Definition sum : bag -> bag -> bag := app.

  Example test_sum1 : count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.

  Definition add (v : nat) (s : bag) : bag := v :: s.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint member (v : nat) (s : bag) : bool :=
    match s with
    | nil => false
    | h :: t => if v =? h then true else member v t
    end.

  Example test_member1: member 1 [1;4;1] = true.
  Proof. reflexivity. Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof. reflexivity. Qed.

  (* Exercise bag_more_function *)
  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
    | nil => nil
    | h :: t => if h =? v then t else h :: remove_one v t
    end.

  Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;4;1]) = 2.
  Proof. reflexivity. Qed.

  Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed.


  Fixpoint remove_all (v : nat) (s : bag) : bag :=
    match s with
    | nil => nil
    | h :: t => if h =? v then remove_all v t else h :: remove_all v t
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint included (s1 : bag) (s2 : bag) : bool :=
    match s1, s2 with
    | nil, _ => true
    | h :: t, s2' => if member h s2'
                  then included t (remove_one h s2')
                  else false
    end.

  Example test_included1: included [1;2] [2;1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_included2: included [1;2;2] [2;1;4;1] = false.
  Proof. reflexivity. Qed.

  (* exercise add_inc_count *)

  Print count.
  
  Theorem add_inc_count : forall c n : nat, forall b : bag,
      (count c b) = n -> count c (add c b) = S n.
  Proof.
    intros c n.
    intros b.
    intros H.
    simpl.
    case_eq ( c =? c).
    - intros H1.
      rewrite -> H.
      reflexivity.
    - intros H1.
      rewrite -> eqb_refl in H1.
      inversion H1.
    Qed.

(*
  it is important to step through the details of each one
  using Coq and think about what each step achieves.
 *)

  (*  useful commands : Search Check Compute Print *)

  (* Induction on Lists *)
  Theorem app_assoc : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3.
    induction l1 as [| n l1' IHl'].
    - reflexivity.
    - simpl.
      rewrite -> IHl'.
      reflexivity.
  Qed.
  
  (* reversing a list *)
  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  (* exercise *)
  Theorem app_nil_r : forall l : natlist, l ++ [] = l.
  Proof.
    intros l.
    induction l as [| n l' IHl']. (* IHl': l' ++ [] = l' *)
    - reflexivity.
    - simpl.
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem rev_app_distr : forall l1 l2 : natlist,
      rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2.
    induction l1 as [|n l1' IHl'].
    - simpl.
      rewrite -> app_nil_r.
      reflexivity.
    - simpl.
      rewrite -> IHl'.
      rewrite -> app_assoc.
      reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
  Proof.
    intros l.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. (* rev (rev (n::l')) = n::l' *)
      rewrite -> rev_app_distr.
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3)++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_assoc.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl.
      case_eq (n =? 0).
      + intro IHn.
        rewrite -> IHl1'.
        reflexivity.
      + intro IHn.
        simpl.
        rewrite -> IHl1'.
        reflexivity.
  Qed.

  (* exercise eqblist *)
  Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _l2' => false
  | _l1', nil => false
  | h1 :: t1, h2 :: t2 => if h1 =? h2 then eqblist t1 t2 else false
  end.

  Example test_eqblist1 : (eqblist nil nil = true).
  Proof. reflexivity. Qed.

  Example test_eqblist2 : (eqblist [1;2;3] [1;2;3] = true).
  Proof. reflexivity. Qed.

  Example test_eqblist3 : (eqblist [1;2;3] [1;2;4] = false).
  Proof. reflexivity. Qed.

  Theorem eqblist_refl : forall l : natlist, true = eqblist l l.
  Proof.
    intros l.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl.
      case_eq (n =? n).
      + intros H.
        rewrite <- IHl'.
        reflexivity.
      + intros H.
        rewrite eqb_refl in H.
        inversion H.
  Qed.
        
  Theorem count_memeber_nonzero : forall (s : bag),
      1 <=? (count 1 (1 :: s)) = true.
  Proof.
    intros s.
    induction s as [| n s' IHs'].
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem leb_n_Sn : forall n, n <=? (S n) = true.
  Proof.
    intros n.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
  Qed.

  Theorem remove_does_not_increase_count : forall (s : bag),
      (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
  Proof.
    intros s.
    induction s as [|n s' IHs'].
    - reflexivity.
    - induction n as [| n'].
      + simpl. apply leb_n_Sn.
      + simpl. apply IHs'.
  Qed.

  Theorem involution_injective : forall (f : nat -> nat),
      (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
  Proof.
    
    intros.    
  Abort. 
    (* no idea for now 
    intros f.
    intros F. 
    intros n1 n2.
    intros F1.
    induction n1 as [| n1' IHn1'].
    - intros n0.
      induction n0 as [| n0' IHn0'].
      + simpl.                        
     *)
  
  Theorem rev_injecttive : forall (l1 l2 : natlist),
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H.
  Abort.
  
  (* Option *)
  Inductive natoption : Type :=
  | Some (n : nat)
  | None.

  Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
    match l with
    | nil => None
    | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
    end.

  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.

  Definition hd_error (l : natlist) : natoption :=
    match l with
    | nil => None
    | h :: t => Some h
    end.
  Example test_hd_error1 : hd_error [] = None.
  Proof. reflexivity. Qed.
  Example test_hd_error2 : hd_error [1] = Some 1.
  Proof. reflexivity. Qed.
  Example test_hd_error3 : hd_error [5;6] = Some 5.
  Proof. reflexivity. Qed.

  Theorem option_elim_hd : forall (l : natlist) (default : nat),
      hd default l = option_elim default (hd_error l).
  Proof.
    intros.
    induction l as [|n l' IHl'].
    - reflexivity.
    - reflexivity.
  Qed.  
End NatList.

(* Partial Maps *)
Inductive id : Type := | Id (n : nat).
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  intros x.
  induction x.
  simpl.
  apply eqb_refl.
Qed.

Module PartialMap.
  Export NatList.

  Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

  Definition update (d : partial_map)
    (x : id) (value : nat) : partial_map :=
    record x value d.

  Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                    then Some v
                    else find x d'
  end.

  Theorem update_eq : forall (d : partial_map) (x : id) (v : nat),
      find x (update d x v) = Some v.
  Proof.
    intros.
    simpl.
    case_eq ( eqb_id x x).
    - intros H. reflexivity.
    - intros H.
      rewrite -> eqb_id_refl in H.
      inversion H.
  Qed.

  Theorem update_neq : forall (d : partial_map) (x y : id) (o : nat),
      eqb_id x y = false -> find x (update d y o) = find x d.
  Proof.
    intros.
    simpl.
    case_eq (eqb_id x y).
    - intros.
      rewrite H in H0.
      inversion H0.
    - intros.
      reflexivity.
  Qed.
  
End PartialMap.

(*  Two Abort need to take case of *)
