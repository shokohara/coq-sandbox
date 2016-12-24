Definition prop0 : forall (A : Prop), A -> A.
Proof.
intros.
apply H.
Qed.

Theorem prop0' : forall (A : Prop), A -> A.

Lemma prop0'' : forall (A : Prop), A -> A.

Example prop0''' : forall (A : Prop), A -> A.
Example prop0'''' : forall (A : Prop), A -> A := fun A x => x.

Goal forall (A : Prop), A -> A.

Goal forall (P Q : Prop), (forall P : Prop, (P -> Q) -> Q) -> ((P -> Q) -> P) -> P.
intro.
intro.
intro.
intro.
apply H0.
intro.
apply (H (P -> Q)).
apply (H P).
Qed.

Goal forall (P Q : Prop), (forall P : Prop, (P -> Q) -> Q) -> ((P -> Q) -> P) -> P.
Proof.
intros.
apply H0.
intros.
apply (H Q).
intro.
apply H2.
Qed.

Goal forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros.
  apply (H0 (H H1)).
Qed.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Inductive False : Prop :=.

Definition not (A : Prop) := A -> False.

Goal forall P : Prop, P -> ~~P.
  intros.
  intro.
  apply H0.
  apply H.
Qed.
  
Goal forall P : Prop, P -> ~~P.
  unfold not.
  intros.
  intro.
  apply H0.
  apply H.
Qed.

(*
Goal forall P : Prop, P -> not (not P).
  intros.
  intro.
  apply H0.
  apply H.
Qed.
 *)

Inductive or (A B : Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.

(*
Goal forall (P Q : Prop), P \/ Q -> Q \/ P.
  intros.
  case H.
  apply or_intror.
  apply or_introl.
Qed.
*)

Goal forall (P Q : Prop), P \/ Q -> Q \/ P.
  intros.
  destruct H.
  right.
  apply H.
  left.
  apply H.
Qed.

Inductive and (A B : Prop) : Prop :=
  conj : A -> B -> and A B.

(*
Goal forall (P Q : Prop), P /\ Q -> Q /\ P.
  intros.
  destruct H.
  apply conj.
 *)

Goal forall (P Q : Prop), P /\ Q -> Q /\ P.
  intros.
  destruct H.
  split.
  apply H0.
  apply H.
Qed.

Goal forall (P : Prop), P -> ~~P.
  auto.
Qed.

Goal forall (P Q : Prop), P \/ Q -> Q \/ P.
  tauto.
Qed.

Goal forall (P Q : Prop), P /\ Q -> Q /\ P.
  tauto.
Qed.

Goal forall (P : Prop), ~(P /\ ~P).
  intros.
  intro.
  destruct H.
  apply H0.
  apply H.
Qed.

Goal forall (P Q : Prop), ~P \/ ~Q -> ~(P /\ Q).
  intros.
  intro.
  destruct H.
  apply H.
  destruct H0.
  apply H0.
  apply H.
  destruct H0.
  apply H1.
Qed.

(*
Goal forall (P : Prop), (forall (P : Prop), ~~P -> P) -> P \/ ~P.
  intros.
  left.
  apply (H P).
  intro.
  apply H0.
  apply (H P).
  intro.
  apply (H0).
 *)

(*
Goal forall (P : Prop), (forall (P : Prop), ~~P -> P) -> P \/ ~P.
  intros.
  left.
  apply H.
  intro.
  apply H0.
  apply (H P).
  intro.
  apply (H (~P)).
 *)

(*
Goal forall (P : Prop), (forall (P : Prop), ~~P -> P) -> P \/ ~P.
  intros.
  left.
  apply (H P).
  intro.
  apply H0.
  apply H.
  apply (H (~~P)).
  intro.
  apply 
 *)

(*
Goal forall (P : Prop), (forall (P : Prop), ~~P -> P) -> P \/ ~P.
  unfold not.
  intros.
  apply H.
Qed.
 *)

Goal forall (P : Prop), (forall (P : Prop), ~~P -> P) -> P \/ ~P.
  intros.
  apply (H (P \/ (~P))).
  intros.
  intro.
  apply H0.
  intros.
  right.
  intro.
  apply H0.
  left.
  apply H1.
Qed.
