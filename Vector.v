Inductive Fin : nat -> Type :=
  | First : forall n, Fin (S n)
  | Next  : forall n, Fin n -> Fin (S n).

Inductive empty : Set := .

Fixpoint myFin (n : nat) : Set :=
  match n with
  | 0 => empty
  | S n => (unit + myFin n) % type
  end.

Lemma Fin_0 (B : Type) : Fin 0 -> B.
intros B e.
inversion e.
Qed.

(*
Lemma Fin_S : forall 

Fixpoint aa (n : nat) : Fin n -> myFin n :=
  match n return Fin n -> myFin n with
  | 0   => fun i : Fin 0 => Fin_0 (myFin 0) i
  | S n => fun i : Fin (S n) =>
    match i with 
    | First n  => inl (myFin n) tt
    | Next n i => inr unit (aa n i)
    end
  end.
*)

Definition aa : forall n, Fin n -> myFin n.
induction n as [|n IH]; intro i.
inversion i.
inversion_clear i.
exact (inl (myFin n) tt).
exact (inr unit (IH H)).
Defined.

(*
Definition bb : forall n, myFin n -> Fin n.
*)

Set Implicit Arguments.

Section vectors.

Variable A : Type.

Definition vector (n : nat) := myFin n -> A.

Definition nil : vector 0 := (empty_rect (fun _ => A)).

Definition cons : forall n, A -> vector n -> vector (S n) :=
  fun n a v i => 
  match i with 
  | inl tt => a
  | inr i' => v i'
  end.

Definition head (n : nat) (v : vector (S n)) : A :=
  v (inl (myFin n) tt).

Definition tail (n : nat) (v : vector (S n)) : vector n :=
  fun i : myFin n => (v (inr unit i)).

(*
Variables a b : A.

Definition v : vector 2 :=
  fun i => match i with inl tt => a | inr i' => b end.

Eval compute in (tail v).
*)


(*
Definition vector (n : nat) := Fin n -> A.

Definition head (n : nat) (v : vector (S n)) : A :=
  v (First n).

Definition tail (n : nat) (v : vector (S n)) : vector n :=
  fun i : Fin n => (v (Next n i)).

*)

End vectors.
