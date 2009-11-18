Set Implicit Arguments.

(* 
  thanks to Adam Chlipala for suggesting this representation of vector,
  and for showing how easy some constructions (cons,map) over them can be defined;
  see the following thread in the mails archive of the coqclub mailing list:
  http://logical.saclay.inria.fr/coq-puma/messages/9978d9af68461f02
*)

Inductive Fin : nat -> Type :=
  | First : forall n, Fin (S n)
  | Next  : forall n, Fin n -> Fin (S n).

Lemma Fin_0_inv (A : Type) : Fin 0 -> A.
inversion 1.
Qed.

Section vectors.

Variable A : Type.

Definition vector (n : nat) := Fin n -> A.

Definition vnil : vector 0 := Fin_0_inv A.

Definition vcons (x : A) n (v : vector n) : vector (S n) :=
  let P := 
    fun k =>
    match k return Type with
    | O   => Empty_set
    | S n => vector n -> A
    end
  in
    fun i =>
    match i in Fin Sn return P Sn with
    | First _   => fun _ => x
    | Next _ i' => fun v => v i'
    end v.

(* compare this to (with the definition of vector using myFin (see myVector.v): *)
(*
Definition myvcons : A -> forall n, myvector n -> myvector (S n) :=
  fun a n v i => 
  match i with 
  | inl tt => a
  | inr i' => v i'
  end.
*)

Definition vhead (n : nat) (v : vector (S n)) : A :=
  v (First n).

Definition vtail (n : nat) (v : vector (S n)) : vector n :=
  fun i : Fin n => v (Next i).

End vectors.

Implicit Arguments First [n].

Section map.

Variables (A B : Type) (f : A -> B).

Definition vmap (n : nat) : vector A n -> vector B n :=
  fun v i => f (v i).

End map.

Section fold.

Variables (A B : Type) (b : B) (f : A -> B -> B).

Fixpoint vfold (n : nat) : vector A n -> B :=
  match n with 
  | O   => fun _ => b
  | S n => fun v => f (vhead v) (vfold (vtail v))
  end.

End fold.

Section function_composition.

Variables (A B C : Type) (f : B -> C) (g : A -> B).
Definition compose : A -> C := 
  fun x => f (g x).

End function_composition.

Notation "f * g" := (compose f g).
