Require Import Vector.

Set Implicit Arguments.

Inductive empty : Set := .

Definition from_empty (A : Type) : empty -> A :=
  fun e => match e with end.

Fixpoint myFin (n : nat) : Set :=
  match n with
  | 0 => empty
  | S n => (unit + myFin n) % type
  end.

Definition myFirst (n : nat) : myFin (S n) :=
  inl (myFin n) tt.

Definition myNext (n : nat) : myFin n -> myFin (S n) :=
  fun i => inr unit i.

Definition Fin2myFin : forall n, Fin n -> myFin n.
induction n as [|n IH]; intro i.
inversion i.
inversion_clear i.
exact (inl (myFin n) tt).
exact (inr unit (IH H)).
Defined.

Definition myFin2Fin : forall n, myFin n -> Fin n.
Admitted. (* uebnung *)

(* Note that
   all we can do with [i : Fin (S n)] is [inversion i] 
   (and build ugly proof terms with dependent elimination predicates).
   on the other hand, to [i : myFin (S n)] we can simply say [destruct i],
   yielding a match expression on the term level.
*)

Section myvector.

Variable A : Type.

Definition myvector (n : nat) := myFin n -> A.

Definition myvnil : myvector 0 := from_empty A.

Definition myvcons : A -> forall n, myvector n -> myvector (S n) :=
  fun a n v i => 
  match i with 
  | inl tt => a
  | inr i' => v i'
  end.

Definition myvhead (n : nat) (v : myvector (S n)) : A :=
  v (inl (myFin n) tt).

Definition myvtail (n : nat) (v : myvector (S n)) : myvector n :=
  fun i : myFin n => (v (inr unit i)).

End myvector.

Section map.

Variables (A B : Type) (f : A -> B).

Fixpoint myvmap (n : nat) : myvector A n -> myvector B n :=
  match n with 
  | O   => fun _ => myvnil B
  | S n => fun v => myvcons (f (myvhead v)) (myvmap (myvtail v))
  end.

End map.

Section fold.

Variables (A : Type) (a : A) (f : A -> A -> A).

Fixpoint myvfold (n : nat) : myvector A n -> A :=
  match n with 
  | O   => fun _ => a
  | S n => fun v => f (myvhead v) (myvfold (myvtail v))
  end.

End fold.
