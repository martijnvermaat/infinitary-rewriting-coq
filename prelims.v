Set Implicit Arguments.

Definition S_eq : forall (n m : nat), n = m -> S n = S m := 
  fun n m H => f_equal S H.

(*
Definition aha := 
fun (n m : nat) (Sn_eq_Sm : S n = S m) =>
let H := refl_equal (n = m) in
eq_rect 
  (pred (S n) = pred (S m)) 
  (fun P : Prop => P)
  (eq_rect (S m) 
           (fun n0 : nat => pred n0 = pred (S m)) 
           (refl_equal (pred (S m))) 
           (S n) 
           (sym_eq Sn_eq_Sm)
  ) 
  (n = m) 
  H.
*)

Definition disc_O_S : forall (n : nat), O <> S n :=
  fun n H =>
  let P := (fun q : nat => match q with 0 => (False -> False) | S q => False end) in 
  match H in (_ = q) return P q with refl_equal => (fun a => a) end.

Definition disc_S_O : forall (n : nat), S n <> O :=
  fun n H => disc_O_S (sym_eq H).