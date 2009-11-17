Set Implicit Arguments.

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

(*
Definition vcons : A -> forall n, vector n -> vector (S n).
intros a [|n]; intros v i.
exact a.
inversion_clear i as [| n' i' H].
exact a.
exact (v i').
Defined.

Print vcons.
*)

Definition vcons : A -> forall n, vector n -> vector (S n) :=
  fun a n =>
  match n return vector n -> vector (S n) with
  | O   => fun _ _ => a
  | S n => 
      fun (v : vector (S n)) (i : Fin (S (S n))) =>
      let X :=
        match i in Fin m return S (S n) = m -> A with 
        | First _   => fun _ => a
        | Next m i' => 
            fun (H : S (S n) = S m) => 
            eq_rect (S n) (fun n1 => Fin n1 -> A) v m 
              (f_equal (fun e => match e with 0 => m | S n1 => n1 end) H) i'
        end 
      in X (refl_equal (S (S n)))
  end.

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
  fun i : Fin n => (v (Next i)).

End vectors.

Implicit Arguments First [n].

Section map.

Variables (A B : Type) (f : A -> B).

Fixpoint vmap (n : nat) : vector A n -> vector B n :=
  match n with 
  | O   => fun _ => vnil B
  | S n => fun v => vcons (f (vhead v)) (vmap (vtail v))
  end.

End map.

Section fold.

Variables (A : Type) (a : A) (f : A -> A -> A).

Fixpoint vfold (n : nat) : vector A n -> A :=
  match n with 
  | O   => fun _ => a
  | S n => fun v => f (vhead v) (vfold (vtail v))
  end.

End fold.
