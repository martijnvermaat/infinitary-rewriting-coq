Require Import prelims.

Set Implicit Arguments.

Inductive empty : Set := .

Fixpoint Fin (n : nat) : Set :=
  match n with
  | O   => empty
  | S n => (unit + Fin n) % type
  end.

Definition First (n : nat) : Fin (S n) :=
  inl (Fin n) tt.

Definition Next (n : nat) : Fin n -> Fin (S n) :=
  fun i => inr unit i.

Section vector.

Variable A : Type.

Definition vector (n : nat) := Fin n -> A.

Definition vnil : vector 0 :=
  fun e => match e with end.

Definition vcons : A -> forall n, vector n -> vector (S n) :=
  fun a n v i => 
  match i with 
  | inl tt => a
  | inr i' => v i'
  end.

Definition vhead (n : nat) (v : vector (S n)) : A :=
  v (inl (Fin n) tt).

Definition vtail (n : nat) (v : vector (S n)) : vector n :=
  fun i : Fin n => (v (inr unit i)).

Fixpoint vappend (n m : nat) : vector n -> vector m -> vector (n + m) :=
  match n return vector n -> vector m -> vector (n + m) with
  | 0    => fun _ w => w
  | S n' => fun v w => vcons (vhead v) (vappend (vtail v) w)
  end.

Lemma vcons_vhead_vtail : 
  forall n (v : vector (S n)) (i : Fin (S n)),
  vcons (vhead v) (vtail v) i = v i.
Proof.
intros n v [[]|i]; reflexivity.
Qed.

(* Just curious *)
Definition ext_eq : Prop := forall A B (f g : A -> B), (forall x, f x = g x) -> f = g.

Lemma vcons_vhead_vtail' :
  ext_eq ->
  forall n (v : vector (S n)),
  vcons (vhead v) (vtail v) = v.
Proof.
intros H n v; apply H; apply vcons_vhead_vtail.
Qed.

Lemma vtail_vcons : 
  forall a n (v : vector n) (i : Fin n), 
  vtail (vcons a v) i = v i.
Proof.
reflexivity.
Qed.

End vector.

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

Section cast.

Variable A : Type.

Definition vcast n (v : vector A n) m (H : n = m) : vector A m :=
  match H in (_ = m) return vector A m with 
  | refl_equal => v
  end.

Require Import Equality.

Lemma vcast_vcons : 
  forall (a : A) n (v : vector A n) m (H : S n = S m) (i : Fin (S m)),
  vcast (vcons a v) H i = vcons a (vcast v (S_eq_inv H)) i.
Proof.
intros a n v m H i.
dependent destruction H.
reflexivity.
Qed.

(*
Lemma vcast_pi :
  forall n (v : vector A n) m (H H' : n = m),
  vcast v H = vcast v H'.
*)

End cast.
