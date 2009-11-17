Inductive Fin : nat -> Type :=
  | First : Fin 1
  | Next  : forall n, Fin n -> Fin (S n).

Definition vector (A : Type) (n : nat) :=
  Fin n -> A.

Implicit Arguments vector [A].