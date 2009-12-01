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

Definition vhead (n : nat) (v : vector (S n)) : A :=
  v (First n).

Definition vtail (n : nat) (v : vector (S n)) : vector n :=
  fun i : Fin n => v (Next i).

Lemma vcons_vhead_vtail : 
  forall n (v : vector (S n)) (i : Fin (S n)),
  vcons (vhead v) (vtail v) i = v i.
Proof.
intros n v i.
(* gedoe, zie Vector2.v *)
Admitted.

Lemma vtail_vcons : 
  forall a n (v : vector n) (i : (Fin n)), 
  vtail (vcons a v) i = v i.
Proof.
reflexivity.
Qed.

Fixpoint vappend (n m : nat) : vector n -> vector m -> vector (n + m) :=
  match n return vector n -> vector m -> vector (n + m) with
  | O    => fun _ w => w
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

Section cast.

Variable A : Type.

Definition vcast n (v : vector A n) m (H : n = m) : vector A m :=
  match H in (_ = m) return vector A m with 
  | refl_equal => v
  end.

Lemma vcast_pi :
  forall n (v : vector A n) m (H H' : n = m),
  vcast v H = vcast v H'.
Admitted.

(*
Lemma vcast_vcons : 
  forall (a : A) n (v : vector A n) m (H : S n = S m),
  vcast (vcons a v) H = vcons a (vcast v (S_eq_inv H)).
Proof.
intros.
Admitted.
*)

(*
Lemma vcast_vcons : 
  forall (a : A) n (v : vector A n) m (H : n = m) (H0 : S n = S m),
  vcast (vcons a v) H0 = vcons a (vcast v H).
*)


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

End cast.
