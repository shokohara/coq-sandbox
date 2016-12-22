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
