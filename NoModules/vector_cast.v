Require Import Bvector.

Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

Set Implicit Arguments.

Section casting.

Variable A : Type.

Definition S_eq : forall (n m : nat), n = m -> S n = S m := 
  fun n m H => f_equal S H.

Definition S_eq_inv : forall (n m : nat), S n = S m -> n = m := 
  fun n m H => eq_add_S n m H.

Definition disc_O_S : forall (n : nat), O <> S n :=
  fun n H =>
  let P := (fun q : nat => match q with 0 => (False -> False) | S q => False end) in 
  match H in (_ = q) return P q with refl_equal => (fun a => a) end.

Definition disc_S_O : forall (n : nat), S n <> O :=
  fun n H => disc_O_S (sym_eq H).

Fixpoint vector_cast (n : nat) (v : vector A n) (m : nat) {struct v} : 
  n = m -> vector A m :=
  match v in (vector _ p) return (p = m -> (vector A m)) with
    Vnil =>
      match m return 0 = m -> vector A m with
        0 => fun _ => Vnil
      | m' => fun H => False_rect (vector A m') (disc_O_S H)
      end
  | Vcons a n' v' => 
	  match m return S n' = m -> vector A m with
	    0    => fun H => False_rect (vector A 0) (disc_S_O H)
	  | S m' => fun H => Vcons a (vector_cast v' (S_eq_inv H))
	  end
  end.

Lemma vector_cast_proof_irrelevance :
  forall (n : nat) (v : vector A n) (m : nat) (H1 H2 : n = m),
  vector_cast v H1 = vector_cast v H2.
Proof.
induction v as [|a n v IH]; destruct m as [|m]; simpl; intros H1 H2.
reflexivity.
discriminate H1.
discriminate H1.
apply f_equal.
apply IH.
Qed.

Lemma vector_cast_elim : forall (n : nat) (v : vector A n) (H : n = n),
  vector_cast v H = v. 
Proof.
induction v as [|a n v IH]; intro H; simpl.
reflexivity.
apply f_equal.
pattern v at 2.
rewrite <- (IH (S_eq_inv H)).
reflexivity.
Qed.

(* alternatively ... *)
Definition vector_cast2 (n : nat) (v : vector A n) (m : nat) (H : n = m) : vector A m :=
  match H in (_ = m) return (vector A m) with
    refl_equal => v
end.

(*
Require Import Equality.

Lemma vector_cast2_Vcons : 
  forall (n : nat) (v : vector A n) (m : nat) (H : n = m) (a : A), 
  vector_cast2 (Vcons a v) (S_eq H) = Vcons a (vector_cast2 v H).
Proof.
intros n v m H a.
dependent destruction H; simpl.
reflexivity.
Qed.
*)

(* but how to prove:
Lemma vector_cast2_proof_irrelevance :
  forall (n : nat) (v : vector A n) (m : nat) (H1 H2 : n = m),
  vector_cast v H1 = vector_cast v H2.
*)

End casting.
