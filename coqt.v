(* 二つの自然数の和を返す *)
Definition plus (n m : nat) : nat := n + m.
Eval compute in plus 3 5.

Definition plus' : nat -> nat -> nat := fun n m => n + m.
Eval compute in plus' 3 5.

Definition id (A : Type)(x : A) : A := x.
Eval compute in id nat 5.
