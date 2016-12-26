Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Require Import List.

Fixpoint app (A : Type)(l l' : list A) : list A :=
  match l with
  | nil => l'
  | cons x xs => cons x (app A xs l')
  end.

Theorem app_nil_r : forall (A : Type)(l : list A), l ++ nil = l.
  intros.
  induction l.
  reflexivity.
  simpl.
  apply(f_equal(cons a)).
  apply IHl.
Qed.

Goal forall (A : Type)(l : list A), l ++ nil = l.
  intros.
  induction l.
  reflexivity.
  simpl.
  f_equal.
  apply IHl.
Qed.

Require Import List.
Theorem app_assoc : forall (A : Type)(l1 l2 l3 : list A), l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
  intros.
  induction l1.
  reflexivity.
  simpl.
  f_equal.
  apply IHl1.
Qed.

Theorem rev_app_distr : forall (A : Type)(l1 l2 : list A), rev (l1 ++ l2) = rev l2 ++ rev l1.
  intros.
  induction l1.
  simpl.
  rewrite app_nil_r.
  reflexivity.
  simpl.
  rewrite app_assoc.
  f_equal.
  apply IHl1.
Qed.
(*
Require Import List.
Theorem rev_involutive : forall (A : Type)(l : list A), rev (rev l) = l.
  intros.
  induction l.
  reflexivity.
  simpl.
Qed.
*)

Require Import List.
Theorem fold_right_app : forall (A B : Type)(f : B -> A -> A)(l l' : list B)(i : A),
    fold_right f i (l ++ l') = fold_right f (fold_right f i l') l.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  f_equal.
  apply IHl.
Qed.

(*
Fixpoint fold_right (A B : Type)(f : B -> A -> A)(a0 : A)(l : list B) : A :=
  match l with
  | nil => a0
  | b :: t => f b (fold_right A B f a0 t)
  end.
Theorem fold_right_app : forall (A B : Type)(f : B -> A -> A)(l l' : list B)(i : A),
    fold_right f i (l ++ l') = fold_right f (fold_right f i l') l.
  intros.
 *)
