(*
   Below we try to separate the good from the bad
*)

(* We would like to Import this, but then we need to copy a lot of
   lemmas from ord' to ord... *)
Require Export PreOrdinals.

Set Implicit Arguments.


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

Lemma nat_good :
  forall (n : nat), good n.
Proof.
induction n.
exact I.
assumption.
Qed.

(*
Axiom good_pi : forall alpha (H H' : good alpha), H = H'.
*)

(*
Lemma good_pi : forall alpha (H H' : good alpha), H = H'.
induction alpha as [|alpha' IH|f IH]; simpl; intros H H'.
case H; case H'; reflexivity.
apply IH.

(*

H : forall n, P n /\ Q n

p : forall n, P n

H = fun n => conj (p n) (q n)

*)
*)

(*
Lemma aa :
  forall p q : Prop, forall H H' : p -> True, H = H'.
intros.

replace H with (fun H : p => I).
Focus 2.
reflexivity.
*)

Definition ord : Set := sig good.

Axiom ord_pi :
  forall alpha (H H' : good alpha),
    exist good alpha H = exist good alpha H'.

Implicit Arguments ord_pi [alpha].

Definition zero : ord := exist good Zero I.

(*
(* TODO: the let bindings don't play nice with alpha conversion *)
Definition succ (alpha : ord) : ord :=
  let (alpha', H) := alpha in
    exist g'' (Succ alpha') H.
*)
Definition succ (alpha : ord) : ord :=
(*  let (alpha', H) := alpha in
    exist good (Succ alpha') H.*)
  exist good (Succ (proj1_sig alpha)) (proj2_sig alpha).

Definition limit (f : nat -> ord) H : ord :=
  exist good
    (Limit (fun n => proj1_sig (f n)))
    (fun n => conj (proj2_sig (f n)) (H n)).

Definition is_succ (o : ord) : Prop :=
  match proj1_sig o with
  | Succ _ => True
  | _      => False
  end.

Definition is_limit (o : ord) : Prop :=
  match proj1_sig o with
  | Limit _ => True
  | _       => False
  end.

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
    (exist good alpha Ha) = (exist good beta Hb).
Proof.
intros alpha beta Ha Hb H.
generalize Ha.
rewrite H.
intro Hb'.
apply ord_pi.
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
induction alpha' as [| | f IH].
reflexivity.
elim (ord'_le_not_succ_zero H).
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
Definition nat_as_ord (n : nat) : ord :=
  exist good n (nat_good n).

Coercion nat_as_ord : nat >-> ord.

Definition omega := limit nat_as_ord lt_nat_ord'.

Lemma n_le_omega : forall (n : nat), n <= omega.
Proof.
destruct n as [| n]; unfold ord_le; simpl.
constructor.
apply Ord'_le_Succ with (i := existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord'_le_refl.
Qed.

Lemma n_lt_omega : forall (n : nat), n < omega.
Proof.
intro n.
exists (existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord'_le_refl.
Qed.

(* If alpha < beta, the successor of alpha <= beta *)
Lemma ord_lt_ord_le_succ :
  forall alpha beta,
    alpha < beta ->
    succ alpha <= beta.
Proof.
intros.
unfold succ.
apply ord'_lt_ord'_le_succ.
assumption.
Qed.

(*
   The following lemmas serve to make statements in Rewriting.v as short as
   possible (no projections to ord' etc).
*)

Lemma ord_le_zero :
  forall alpha, zero <= alpha.
Proof.
intro.
apply Ord'_le_Zero.
Qed.

Lemma ord_le_refl :
  forall alpha, alpha <= alpha.
Proof.
intro.
apply ord'_le_refl.
Qed.


Close Scope ord_scope.

Close Scope ord'_scope.
