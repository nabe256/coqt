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

(* Inductive:型定義 *)
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

(* Inductive False : Prop :=. *)

(* Definition:関数定義 *)
(* Definition not (A : Prop) := A -> False. *)

Goal forall (P : Prop), P -> ~~P.
Proof.
  intros.
  intro.
  apply H0.
  apply H.
Qed.

Goal forall (P : Prop), P -> ~~P.
Proof.
  unfold not.
  intros.
  apply H0.
  apply H.
Qed.

(*
Inductive or (A B : Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.
*)

Goal forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
  intros.
  case H. (* 場合分け *)
  apply or_intror.
  apply or_introl.
Qed.

Goal forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
  intros.
  destruct H.
  right.
  apply H.
  left.
  apply H.
Qed.

(*
Inductive and (A B : Prop) : Prop :=
  conj : A -> B -> and A B.
*)

Goal forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H.
  split. (* apply conj. *)
  apply H0.
  apply H.
Qed.

Goal forall (P : Prop), P -> ~~P.
Proof.
  auto. (* info_auto *)
Qed.
