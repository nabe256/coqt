(* 二つの自然数の和を返す *)
Definition plus (n m : nat) : nat := n + m.
Eval compute in plus 3 5.

Definition plus' : nat -> nat -> nat := fun n m => n + m.
Eval compute in plus' 3 5.

Definition id (A : Type)(x : A) : A := x.
Eval compute in id nat 5.

Definition id' : forall (A : Type), A -> A := fun A x => x.
Eval compute in id' nat 5.

Definition prop0 : forall (A : Prop), A -> A :=
  fun A x => x.

Definition prop1 : forall (A B C : Prop), (B -> C) -> (A -> B) -> (A -> C) :=
  fun A B C f g x => f (g x).

Definition ex0 : forall (A B : Prop), A -> (A -> B) -> B :=
  fun A B x f => f x.

Definition ex1 : forall (A B C : Prop), (A -> B -> C) -> (B -> A -> C) :=
  fun A B C f g h => f h g.

Definition prop0' : forall (A : Prop), A -> A.
Proof.
  intros.
  apply H.
Qed.
Print prop0'.

Goal forall (P Q : Prop), (forall P : Prop, (P -> Q) -> Q) -> ((P -> Q) -> P) -> P.
Proof.
  intros. (* intro. intro. intro. intro. *)
  apply H0.
  intro.
  apply (H (P -> Q)).
  apply (H P). (* apply H. *)
  Qed.

Goal forall (P Q : Prop), (forall P : Prop, (P -> Q) -> Q) -> ((P -> Q) -> P) ->  P.
Proof.
  intros.
  apply H0.
  intros.
  apply (H Q).
  intro.
  apply H2.
Qed.

Definition ex2 : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.
