Set Implicit Arguments.

Notation "!" := (False_rect _).

Definition S_eq : forall (n m : nat), n = m -> S n = S m :=
  fun n m H => f_equal S H.

(*
Definition S_eq_inv : forall (n m : nat), S n = S m -> n = m :=
  fun n m H => eq_add_S n m H.
*)

Definition S_eq_inv : forall (n m : nat), S n = S m -> n = m :=
  fun (n m : nat) (H : S n = S m) =>
  match (sym_eq H) in (_ = Sn) return pred Sn = pred (S m) with
  | refl_equal => refl_equal (pred (S m))
end.

Definition disc_O_S : forall (n : nat), O <> S n :=
  fun n H =>
  let P := (fun q : nat => match q with 0 => (False -> False) | S q => False end) in
  match H in (_ = q) return P q with refl_equal => (fun a => a) end.

Definition disc_S_O : forall (n : nat), S n <> O :=
  fun n H => disc_O_S (sym_eq H).
