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

Lemma vtail_vcons : forall a n (v : vector n), vtail (vcons a v) = v.
Proof.
intros a n v.
unfold vtail; simpl.
(* wat nu ... geen eta gelijkheid in Coq ... *)
Admitted.

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

Definition S_eq_inv : forall (n m : nat), S n = S m -> n = m := 
  fun n m H => eq_add_S n m H.

Lemma vcast_vcons : 
  forall (a : A) n (v : vector A n) m (H : S n = S m),
  vcast (vcons a v) H = vcons a (vcast v (S_eq_inv H)).
intros.


dependent inversion H.


or

Lemma vcast_vcons : 
  forall (a : A) n (v : vector A n) m (H : n = m) (H0 : S n = S m),
  vcast (vcons a v) H0 = vcons a (vcast v H).

or

*)



Definition disc_O_S : forall (n : nat), O <> S n :=
  fun n H =>
  let P := (fun q : nat => match q with 0 => (False -> False) | S q => False end) in 
  match H in (_ = q) return P q with refl_equal => (fun a => a) end.

Definition disc_S_O : forall (n : nat), S n <> O :=
  fun n H => disc_O_S (sym_eq H).

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
    | S m' => fun H i => match i with
First => vhead v
| Next i' => (vcast v H) i'
 (vcast (vtail v) (S_eq_inv H))
    end
  end.
*)
 
Lemma bah : 
  forall n (v : vector A (S n)) m (H : S n = m) (i : Fin m),
  (vcast v H) i = vcast (vcons (vhead v) (vtail v)) H i.
Admitted.





Lemma vcast_vtail_vcons_i : 
  forall a n (v : vector A n) (H : n = n) (i : Fin n), 
  vcast (vtail (vcons a v)) H i = v i.
Proof.
Admitted.

End cast.
