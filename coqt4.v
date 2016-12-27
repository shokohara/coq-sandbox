Goal forall (n : nat), n = n + 0.
  intros.
  induction n.
  reflexivity.
  simpl.
  f_equal.
  apply IHn.
Qed.

Require Import Arith.
Goal forall (n : nat), (exists m : nat,  n = m * 4) -> (exists k : nat, n = k * 2).
  intros.
  destruct H.
  exists (x * 2).
  rewrite mult_assoc_reverse.
  simpl.
  apply H.
Qed.

Require Import Arith.

Theorem lt_Snm_nm : forall (n m : nat), S n < m -> n < m.
  intros.
  rewrite lt_n_Sn.
  apply H.
Qed.

Inductive InList (A : Type)(a : A) : list A -> Prop :=
  | headIL : forall xs, InList A a (a :: xs)
  | consIL : forall x xs, InList A a xs -> InList A a (x :: xs).

Require Import List.
Require Import Arith.
Theorem pigeonhole : forall (xs : list nat),
    length xs < fold_right plus 0 xs -> exists x : nat, InList nat (S (S x)) xs.
  intros.
  induction xs.
  simpl in H.
  apply False_ind.
  apply (lt_n_O 0).
  apply H.
  simpl in H.
  destruct a.
  apply lt_Snm_nm in H.
  apply IHxs in H.
  destruct H.
  exists x.
  constructor.
  apply H.
  destruct a.
  simpl in H.
  apply lt_S_n in H.
  apply IHxs in H.
  destruct H. (* H : exists x : ... の時に exists を外すために使う*)
  exists x.
  constructor.
  apply H.
  exists a.
  constructor.
Qed.

Goal forall (n : nat), 0 = n * 0.
trivial.
Qed.

(*
Goal forall (n : nat), 0 = n * 0.
  intros.
  destruct 0.
  simpl.
  reflexivity.
  simpl.
  
Qed.
 *)

Goal forall (n m : nat), n * m = m * n.
auto with arith.
Qed.

(*
Goal forall (n m : nat), n * m = m * n.
  intros.
  destruct n.
Qed.
 *)

Require Import Omega.
Goal forall n m, 1 + 2 * n = 2 * m -> False.
intros.
omega.
Qed.

(*
Goal forall n m, 1 + 2 * n = 2 * m -> False.
intros.
omega.
Qed.
 *)

