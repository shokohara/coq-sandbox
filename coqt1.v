(* 二つの自然数の和を返す *)
(* Definition plus (n m : nat) : nat := n + m. *)

Definition plus n m := n + m.

Definition plus' : nat -> nat -> nat := fun n m => n + m.

Definition id (A : Type)(x : A) : A := x.

Definition id' : forall (A : Type), A -> A := fun A x => x.

Definition prop0' : forall (A : Prop), A -> A := fun A x => x.

Definition prop1 : forall (A B C : Prop), (B -> C) -> (A -> B) -> (A -> C) := fun A B C f g x => f (g x).

(* Definition prop2 : forall (A : Type)(l1 l2 l3 : List A), app l1 l3 = app l2 l3 -> l1 = l2 := ここに定義が入る. *)

Definition prop2 : forall (A B : Prop), A -> (A -> B) -> B := fun A B a b => b a.

(*
Definition prop3 : forall (A B C : Prop), ((A -> B) -> C) -> ((B -> A) -> C) := fun
*)