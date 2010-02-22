Require Import prelims.
Require Import PreOrdinals.
Require Import Equality.

Set Implicit Arguments.

(*
Definition First (n : nat) : Fin (S n) :=
  inl (Fin n) tt.

Definition Next (n : nat) : Fin n -> Fin (S n) :=
  fun i => inr unit i.
*)

Section vector.

Variable A : Type.

Definition vector (alpha : ord') := pred_type alpha -> A.

Definition vnil : vector Zero :=
  fun e => match e with end.

Definition vcons : A -> forall alpha, vector alpha -> vector (Succ alpha) :=
  fun a n v i =>
  match i with
  | inl tt => a
  | inr i' => v i'
  end.

Definition vhead (alpha : ord') (v : vector (Succ alpha)) : A :=
  v (inl (pred_type alpha) tt).

Definition vtail (alpha : ord') (v : vector (Succ alpha)) : vector alpha :=
  fun i : pred_type alpha => (v (inr unit i)).

(*
Fixpoint vappend (n m : nat) : vector n -> vector m -> vector (n + m) :=
  match n return vector n -> vector m -> vector (n + m) with
  | 0    => fun _ w => w
  | S n' => fun v w => vcons (vhead v) (vappend (vtail v) w)
  end.
*)

Lemma vcons_vhead_vtail :
  forall alpha (v : vector (Succ alpha)) (i : pred_type (Succ alpha)),
  vcons (vhead v) (vtail v) i = v i.
Proof.
intros n v [[]|i]; reflexivity.
Qed.

Lemma vtail_vcons :
  forall a alpha (v : vector alpha) (i : pred_type alpha),
  vtail (vcons a v) i = v i.
Proof.
reflexivity.
Qed.

End vector.

Section map.

Variables (A B : Type) (f : A -> B).

Definition vmap (alpha : ord') : vector A alpha -> vector B alpha :=
  fun v i => f (v i).

End map.

(*
Section fold.

Variables (A B : Type) (b : B) (f : A -> B -> B).

Fixpoint vfold (n : nat) : vector A n -> B :=
  match n with
  | O   => fun _ => b
  | S n => fun v => f (vhead v) (vfold (vtail v))
  end.

End fold.
*)

Section cast.

Variable A : Type.

Definition vcast alpha (v : vector A alpha) beta (H : alpha = beta) : vector A beta :=
  match H in (_ = beta) return vector A beta with
  | refl_equal => v
  end.

Definition Succ_eq_inv : forall (alpha beta : ord'), Succ alpha = Succ beta -> alpha = beta :=
  fun (alpha beta : ord') (H : Succ alpha = Succ beta) =>
  match (sym_eq H) in (_ = Salpha) return pred (Succ alpha) (inl (pred_type alpha) tt) = pred (Succ beta) (inl (pred_type beta) tt) with
  | refl_equal => refl_equal (pred (Succ beta) (inl (pred_type beta) tt))
end.

Lemma vcast_vcons :
  forall (a : A) alpha (v : vector A alpha) beta (H : Succ alpha = Succ beta) (i : pred_type (Succ beta)),
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
