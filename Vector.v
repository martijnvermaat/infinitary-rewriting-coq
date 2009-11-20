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

(*
  My problem with vappend here, is that the call to head needs
  n to be > 0, which it of course is after matching with S n'.
  But after this matching, is there any way of showing evidence?

  I firts thought of defining it as a fold using vcons, but of
  course, vcons had the wrong (dependent) types.

  A solution might be to use Program and prove some things
  afterwards, but I can't try it... Coq crashes.
*)

Fixpoint vappend (n m : nat) : vector n -> vector m -> vector (n + m) :=
  match n return vector n -> vector m -> vector (n + m) with
  | 0    => fun _ w => w
  | S n' => fun v w => vcons (vhead v) (vappend (vtail v) w)
  end.

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

(*
Section append.

Variable (A : Type).

(* Of course, this doesn't work because vcons is not A -> B -> B,
   but A -> vector A n -> vector A Sn *)
Definition vappend n m (v : vector A n) (w : vector A m) : vector A (n + m) :=
  vfold w vcons v.

End append.
*)

(* to be done : *)
(*
(* Appending two vectors of lengths n1 and n2 yields a vector of length n1 + n2 *)
Fixpoint vector_append (A : Type) n1 n2 (v1 : vector A n1) (v2 : vector A n2) : vector A (n1 + n2) :=
  match v1 in (vector _ p) return (vector A (p + n2)) with
  | Vnil         => v2
  | Vcons x n xs => Vcons x (vector_append xs v2)
  end.

Implicit Arguments vector_append [A n1 n2].
*)


Section function_composition.

Variables (A B C : Type) (f : B -> C) (g : A -> B).
Definition compose : A -> C :=
  fun x => f (g x).

End function_composition.

Notation "f * g" := (compose f g).
