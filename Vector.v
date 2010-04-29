Require Import Prelims.
Require Import Arith.
Require Import Equality.


Set Implicit Arguments.


(*
  Thanks to Adam Chlipala for suggesting this representation of vector,
  and for showing how easy some constructions (cons,map) over them can be defined;
  see the following thread in the archive of the coqclub mailing list:
  http://logical.saclay.inria.fr/coq-puma/messages/9978d9af68461f02
*)

Inductive Fin : nat -> Type :=
  | First : forall n, Fin (S n)
  | Next  : forall n, Fin n -> Fin (S n).

Lemma Fin_0_inv (A : Type) : Fin 0 -> A.
inversion 1.
Qed.


Section Vector.

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

Definition vhead (n : nat) (v : vector (S n)) : A :=
  v (First n).

Definition vtail (n : nat) (v : vector (S n)) : vector n :=
  fun i : Fin n => v (Next i).

Lemma vcons_vhead_vtail :
  forall n (v : vector (S n)) (i : Fin (S n)),
  vcons (vhead v) (vtail v) i = v i.
Proof.
dependent destruction i; reflexivity.
Qed.

Lemma vtail_vcons :
  forall a n (v : vector n) (i : (Fin n)),
  vtail (vcons a v) i = v i.
Proof.
reflexivity.
Qed.

Program Fixpoint vtake (n m : nat) : n <= m -> vector m -> vector n :=
  match n return n <= m -> vector m -> vector n with
  | O   => fun _ _ => vnil
  | S n => match m return S n <= m -> vector m -> vector (S n) with
           | O   => fun _ _ => False_rect _ _
           | S m => fun _ v => vcons (vhead v) (vtake _ (vtail v))
           end
  end.
Next Obligation.
contradict H.
auto with arith.
Defined.
Next Obligation.
auto with arith.
Defined.

Program Fixpoint vdrop (n m : nat) {struct n} : n <= m -> vector m -> vector (m - n) :=
  match n return n <= m -> vector m -> vector (m - n) with
  | O   => fun _ v => v
  | S n => match m return S n <= m -> vector m -> vector (m - S n) with
           | O   => fun _ _ => False_rect _ _
           | S m => fun _ v => vdrop (n := n) _ (vtail v)
           end
  end.
Next Obligation.
auto with arith.
Defined.
Next Obligation.
contradict H.
auto with arith.
Defined.
Next Obligation.
auto with arith.
Defined.

Program Fixpoint vnth (n m : nat) : n < m -> vector m -> A :=
  match m return n < m -> vector m -> A with
  | O   => fun _ _ => False_rect _ _
  | S m => match n return n < S m -> vector (S m) -> A with
           | O   => fun _ v => vhead v
           | S n => fun _ v => vnth (n := n) _ (vtail v)
           end
  end.
Next Obligation.
contradict H.
auto with arith.
Defined.
Next Obligation.
auto with arith.
Defined.

Fixpoint vappend (n m : nat) : vector n -> vector m -> vector (n + m) :=
  match n return vector n -> vector m -> vector (n + m) with
  | O    => fun _ w => w
  | S n' => fun v w => vcons (vhead v) (vappend (vtail v) w)
  end.

(*
Lemma vtake_vdrop_vappend :
  forall n m (H : m <= n) (v : vector n),
    vappend (vtake H v) (vdrop H v) = v.
*)

End Vector.


Implicit Arguments First [n].


Section Map.

Variables (A B : Type) (f : A -> B).

Definition vmap (n : nat) : vector A n -> vector B n :=
  fun v i => f (v i).

End Map.


Section Fold.

Variables (A B : Type) (b : B) (f : A -> B -> B).

Fixpoint vfold (n : nat) : vector A n -> B :=
  match n with
  | O   => fun _ => b
  | S n => fun v => f (vhead v) (vfold (vtail v))
  end.

End Fold.


Section Cast.

Variable A : Type.

Definition vcast n (v : vector A n) m (H : n = m) : vector A m :=
  match H in (_ = m) return vector A m with
  | refl_equal => v
  end.

Lemma vcast_vcons :
  forall (a : A) n (v : vector A n) m (H : S n = S m) (i : Fin (S m)),
  vcast (vcons a v) H i = vcons a (vcast v (S_eq_inv H)) i.
Proof.
intros a n v m H i.
dependent destruction H.
reflexivity.
Qed.

(*
Fixpoint vcast n : forall (v : vector A n) m (H : n = m), vector A m :=
  match n return forall (v : vector A n) m (H : n = m), vector A m with
  | O   => fun _ m =>
    match m return 0 = m -> vector A m with
      | O => fun _ => (@vnil A)
      | m => fun H => False_rect (vector A m) (disc_O_S H)
      end
  | S n => fun v m =>
    match m return S n = m -> vector A m with
    | O    => fun H => False_rect (vector A 0) (disc_S_O H)
    | S m' => fun H => vcons (vhead v) (vcast (vtail v) (S_eq_inv H))
    end
  end.
*)

End Cast.
