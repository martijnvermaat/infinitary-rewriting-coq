(*
   Below we try to separate the good from the bad
*)

Require Import PreOrdinals.


Open Scope ord'_scope.

Delimit Scope ord_scope with ord.

Open Scope ord_scope.

(* Good ordinals are those where the limit functions are increasing *)
Fixpoint good alpha : Prop :=
  match alpha with
  | Zero      => True
  | Succ beta => good beta
  | Limit f   => forall n, good (f n) /\ forall m, (n < m)%nat -> (f n) <' (f m)
  end.

Axiom good_pi : forall alpha (H H' : good alpha), H = H'.

Definition ord : Set := { alpha : ord' | good alpha }.

Definition g'' := (fun alpha => good alpha).

Definition zero : ord := exist g'' Zero I.

Definition succ (alpha : ord) : ord :=
  let (alpha', H) := alpha in
    exist g'' (Succ alpha') H.

Definition limit (f : nat -> ord) H : ord :=
  exist g''
    (Limit (fun n => proj1_sig (f n)))
    (fun n => conj (proj2_sig (f n)) (H n)).

Definition ord_le (alpha beta : ord) : Prop :=
  proj1_sig alpha <=' proj1_sig beta.
Infix " <= " := ord_le : ord_scope.

Definition ord_lt (alpha beta : ord) : Prop :=
  proj1_sig alpha <' proj1_sig beta.
Infix " < " := ord_lt : ord_scope.

Definition ord_eq (alpha beta : ord) : Prop :=
  proj1_sig alpha ==' proj1_sig beta.
Infix " == " := ord_eq (no associativity, at level 75) : ord_scope.

Lemma ord_eq_ord'_eq :
  forall (alpha beta : ord),
    alpha = beta ->
    proj1_sig alpha = proj1_sig beta.
Proof.
intros alpha beta H.
rewrite H.
reflexivity.
Qed.

Lemma ord'_eq_ord_eq :
  forall (alpha beta : ord') Ha Hb,
    alpha = beta ->
    (exist g'' alpha Ha) = (exist g'' beta Hb).
Proof.
intros alpha beta Ha Hb H.
generalize Ha.
rewrite H.
intro Hb'.
rewrite (good_pi beta Hb' Hb).
reflexivity.
Qed.

(* For any good alpha <= zero, alpha = zero *)
Lemma ord_le_zero_good :
  forall alpha,
    alpha <= zero ->
    alpha = zero.
Proof.
intros alpha H.
destruct alpha as [alpha' G].
apply ord'_eq_ord_eq.
unfold ord_le in H.
simpl in H.
induction alpha' as [| alpha' _ | f IH].
reflexivity.
elim (ord'_le_not_succ_zero alpha' H).
elimtype False.
apply ord'_lt_zero_zero.
simpl in G.
destruct (G 1) as [G1 Gnm].
destruct (G 2) as [G2 _].
inversion_clear H.
pattern Zero at 1.
rewrite <- (IH 1).
rewrite <- (IH 2).
apply Gnm.
constructor.
assumption.
apply H0.
assumption.
apply H0.
Qed.

(* Image of naturals in ordinals *)
Fixpoint nat_as_ord (n : nat) : ord :=
  match n with
  | O   => zero
  | S n => succ (nat_as_ord n)
  end.

(*Coercion nat_as_ord : nat >-> ord.*)

Lemma nat_ord_ord' :
  forall (n : nat),
    proj1_sig (nat_as_ord n) = (nat_as_ord' n).
Proof.
induction n.
reflexivity.
(* TODO *)
Admitted.

(* < on nat is the same as < on ord *)
Require Import Lt. (* For 'auto with arith' *)
(* This proof is een zooitje, but at least it ends with Qed *)
Lemma lt_nat_ord : forall n m, (n < m)%nat <-> nat_as_ord n < nat_as_ord m.
Proof.
intros n m.
unfold ord_lt.
rewrite (nat_ord_ord' n).
rewrite (nat_ord_ord' m).
revert n m.
(* TODO: proof this for new < definition, see below for old proof *)
Admitted.

(*
(* TODO: redo this for new < definition *)
(* < on nat is the same as < on ord *)
Require Import Lt. (* For 'auto with arith' *)
(* This proof is een zooitje, but at least it ends with Qed *)
Lemma lt_nat_ord : forall n m, (n < m)%nat <-> nat_as_ord n < nat_as_ord m.
Proof.
induction n; intro m; split; intro H.
simpl.
destruct H.
split.
constructor.
simpl.
apply ord_le_not_succ_zero.
simpl.
split.
constructor.
apply ord_le_not_succ_zero.
destruct m.
elimtype False.
apply (ord_lt_irrefl (nat_as_ord 0) H).
auto with arith.
simpl.
split.
destruct H.
simpl.
apply Ord_le_Succ with (i := inl (pred_type (Succ (nat_as_ord n))) tt).
apply ord_le_succ_right.
apply ord_le_refl.
simpl.
apply Ord_le_Succ with (i := inl (pred_type (nat_as_ord m)) tt).
elim (IHn m).
intros.
elim H0.
intros.
assumption.
auto with arith.
intro.
destruct m.
contradict H.
auto with arith.
simpl in H0.
assert (H1 := ord_le_succ (nat_as_ord m) (nat_as_ord n) H0).
contradict H1.
elimtype (nat_as_ord n < nat_as_ord m).
intros.
assumption.
apply (IHn m).
auto with arith.
destruct m.
destruct H.
simpl in H.
contradict H.
apply (ord_le_not_succ_zero (nat_as_ord n)).
elimtype (n < m)%nat.
auto with arith.
intros.
auto with arith.
apply (IHn m).
split; destruct H.
apply (ord_le_succ (nat_as_ord n) (nat_as_ord m) H).
intro.
apply H0.
simpl.
apply Ord_le_Succ with (i := inl (pred_type (nat_as_ord n)) tt).
simpl.
assumption.
Qed.
*)

(* TODO: I think proofs like the above would benefit from adding
   some lemma's about ord_le as hints *)

(*
TODO: Weird, why does this not work when Setoid is not required?

  Require Import Setoid.
  Definition omega := Limit id.

But the following does work:

  Definition id' (n : nat) : ord := id n.
  Definition omega := Limit id'.

We have our coercion nat_as_ord, but for some reason it is not used when
the Setoid module is required.
*)
Definition omega := Limit (fun o => o).

Lemma n_le_omega : forall (n : nat), n <= omega.
Proof.
induction n as [| n IH]; simpl; unfold omega.
constructor.
apply Ord_le_Succ with (i := existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord_le_refl.
Qed.

Lemma n_lt_omega : forall (n : nat), n < omega.
Proof.
intro n.
exists (existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord_le_refl.
Qed.

Lemma lt_right : forall alpha beta, alpha <= beta /\ ~ beta <= alpha -> exists i, alpha <= (pred beta i).
Proof.
intros alpha beta H.
destruct H as [H1 H2].

induction beta as [| beta _ | f IH].
(* beta might not be the right choice here... *)

contradict H2.
constructor.

exists (inl (pred_type beta) tt).
simpl.
Admitted.

Lemma lt_left : forall alpha beta, (exists i, alpha <= (pred beta i)) -> alpha <= beta /\ ~ beta <= alpha.
split.

destruct alpha.

constructor.

elim H.
intros.
apply Ord_le_Succ with x.
apply (ord_le_succ_left alpha (pred beta x) H0).

elim H.
intros.
constructor.
inversion_clear H0.
intro.
apply (ord_le_pred_right (o n) beta x).
apply H1.

intro H1.
elim H.
intros.
destruct alpha.

destruct beta.
destruct x.
inversion_clear H1.

Admitted.

Definition is_limit o : Prop := exists f, Limit f = o.

Close Scope ord_scope.

Close Scope ord'_scope.
