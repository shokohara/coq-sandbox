(*
Goal forall (P Q R S : Prop), (S /\ P) /\ (Q /\ R) -> (P /\ S) /\ (R /\ Q).
  intros.
  destruct H.
  split.
  destruct H0.
 *)

Goal forall (P Q R S : Prop), (S /\ P) /\ (Q /\ R) -> (P /\ S) /\ (R /\ Q).
  intros.
  destruct H.
  assert (forall (X Y : Prop), X /\ Y -> Y /\ X).
  intros.
  destruct H1.
  split.
  apply H2.
  apply H1.
  split.
  apply (H1 S P H).
  apply (H1 Q R H0).
Qed.

Goal forall (P Q R S : Prop), (S /\ P) /\ (Q /\ R) -> (P /\ S) /\ (R /\ Q).
  intros.
  destruct H.
  cut (forall (X Y : Prop), X /\ Y -> Y /\ X).
  intro.
  split.
  apply (H1 S P).
  apply H.
  apply (H1 Q R).
  apply H0.
  intros.
  destruct H1.
  split.
  apply H2.
  apply H1.
Qed.

Require Import List.
Theorem app_eq_nil : forall (A : Type)(l l' : list A), l ++ l' = nil -> l = nil /\ l' = nil.
  intros.
  split.
  destruct l.
  reflexivity.
  discriminate.
  destruct l'.
  reflexivity.
  destruct l.
  discriminate.
  discriminate.
Qed.

Require Import List.
Goal forall (A : Type)(a : A), nil <> a :: nil.
  discriminate.
Qed.

Goal forall (n m : nat)(f : nat -> nat), f n = n -> S (f (f n)) = S m -> n = m.
  intros.
  congruence.
Qed.

Goal forall (A : Type)(x y : A), x :: y :: nil <> x :: nil.
  intros.
  congruence.
Qed.

(*
Require Import Arith.
Goal forall (P Q : nat -> Prop)(a : nat), P (a * 2) \/ Q (a * 2).
  intros.
  (*rewrite mult_comm.*)
  replace (Q (a * 2)) with (Q (2 * a)).
  simpl.
 *)

(*
Require Import List.
Lemma removelast_app : forall (A : Type)(l l' : list A), l' <> nil -> removelast (l ++ l') = l ++ removelast l'.
  intros.
  induction l.
  reflexivity.
  simpl.
  destruct (l ++ l').
  remember (l ++ l').
  destruct l0.
  apply False_ind.
  apply H.
  destruct (app_eq_nil l l').
  rewrite Heql0.
  reflexivity.
  apply H1.
  f_equal.
  apply IHl.
 *)

Require Import List.
Inductive InList (A : Type)(a : A) : list A -> Prop :=
  | headIL : forall xs, InList A a (a :: xs)
  | consIL : forall x xs, InList A a xs -> InList A a (x :: xs).

Goal forall (A : Type)(l : list A)(a a' : A), InList A a (a' :: l) -> a = a' \/ InList A a l.
  intros.
  inversion H.
  left.
  reflexivity.
  right.
  apply H1.
Qed.
(*
Goal forall (n : nat), (exists m, n = 2 * m) \/ (exists m, n = 2 * m + 1).
  intros.
  left.
  exists n.
  induction n.
    reflexivity.
    simpl.
    f_equal.
    inversion IHn.
      f_equal.
      intros.
      simpl.
  *)    
      
    
(*    
Require Import Omega.
Goal forall (n : nat), (exists m, n = 2 * m) \/ (exists m, n = 2 * m + 1).
  intros.
  constructor.
  exists n.
  induction n.
  simpl.
  omega.
  simpl.
  induction n.
  simpl.
  apply False_ind.
 *)

(*
Goal forall (A : Type)(l m:list A) (a:A), InList A a (l ++ m) -> InList A a l \/ InList A a m.
  intros.
  left.
  destruct l.
 *)

