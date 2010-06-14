(*
   Below we try to separate the wf from the bad
*)

(* We would like to Import this, but then we need to copy a lot of
   lemmas from ord' to ord... *)
Require Export Ordinal.


Set Implicit Arguments.


Delimit Scope wf_ord_scope with wf_ord.
Open Scope ord_scope.
Open Scope wf_ord_scope.


(* Wf ordinals are those where the limit functions are increasing *)
Fixpoint wf alpha : Prop :=
  match alpha with
  | Zero      => True
  | Succ beta => wf beta
  | Limit f   => forall n, wf (f n) /\ forall m, (n < m)%nat -> (f n) < (f m)
  end.

Lemma nat_wf :
  forall (n : nat), wf n.
Proof.
induction n.
exact I.
assumption.
Qed.

Definition wf_ord : Set := sig wf.

(* Image of wf ordinals in ordinals. *)
Definition wf_ord_as_ord (alpha : wf_ord) : ord :=
  proj1_sig alpha.

Coercion wf_ord_as_ord : wf_ord >-> ord.

(* For any wf alpha <= zero, alpha = zero *)
(* We would like to leave out the explicit coercion here *)
Lemma wf_ord_le_zero_right :
  forall alpha : wf_ord,
    alpha <= Zero ->
    wf_ord_as_ord alpha = Zero.
Proof.
intros alpha H.
destruct alpha as [alpha' G].
simpl in H.
induction alpha' as [| | f IH].
reflexivity.
elim (ord_le_not_succ_zero H).
elimtype False.
apply ord_lt_zero_zero.
simpl in G.
destruct (G 1) as [G1 Gnm].
destruct (G 2) as [G2 _].
inversion_clear H.
pattern Zero at 1.
rewrite <- (IH 1) with G1.
rewrite <- (IH 2) with G2.
apply Gnm.
constructor.
apply H0.
apply H0.
Qed.

Definition zero : wf_ord := exist wf Zero I.

(*
(* TODO: the let bindings don't play nice with alpha conversion *)
Definition succ (alpha : wf_ord) : ord :=
  let (alpha', H) := alpha in
    exist g'' (Succ alpha') H.
*)
Definition succ (alpha : wf_ord) : wf_ord :=
(*  let (alpha', H) := alpha in
    exist wf (Succ alpha') H.*)
  exist wf (Succ (proj1_sig alpha)) (proj2_sig alpha).

Definition limit (f : nat -> wf_ord) H : wf_ord :=
  exist wf
    (Limit (fun n => proj1_sig (f n)))
    (fun n => conj (proj2_sig (f n)) (H n)).

Definition is_succ (o : wf_ord) : Prop :=
  match proj1_sig o with
  | Succ _ => True
  | _      => False
  end.

Definition is_limit (o : wf_ord) : Prop :=
  match proj1_sig o with
  | Limit _ => True
  | _       => False
  end.

Definition wf_ord_le (alpha beta : wf_ord) : Prop :=
  proj1_sig alpha <= proj1_sig beta.
Infix " <wf= " := wf_ord_le (no associativity, at level 75) : wf_ord_scope.

Definition wf_ord_lt (alpha beta : wf_ord) : Prop :=
  proj1_sig alpha < proj1_sig beta.
Infix " <wf " := wf_ord_lt (no associativity, at level 75) : wf_ord_scope.

Definition wf_ord_eq (alpha beta : wf_ord) : Prop :=
  proj1_sig alpha == proj1_sig beta.
Infix " =wf= " := wf_ord_eq (no associativity, at level 75) : wf_ord_scope.

Lemma wf_ord_eq_ord_eq :
  forall (alpha beta : wf_ord),
    alpha = beta ->
    proj1_sig alpha = proj1_sig beta.
Proof.
intros alpha beta H.
rewrite H.
reflexivity.
Qed.

(* Image of naturals in ordinals *)
Definition nat_as_wf_ord (n : nat) : wf_ord :=
  exist wf n (nat_wf n).

Coercion nat_as_wf_ord : nat >-> wf_ord.

Definition wf_omega := limit nat_as_wf_ord lt_nat_ord.

Lemma n_le_omega : forall (n : nat), n <wf= wf_omega.
Proof.
destruct n as [| n]; unfold wf_ord_le; simpl.
constructor.
apply Ord_le_Succ with (i := existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord_le_refl.
Qed.

Lemma n_lt_omega : forall (n : nat), n <wf wf_omega.
Proof.
intro n.
exists (existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord_le_refl.
Qed.

(* If alpha < beta, the successor of alpha <= beta *)
Lemma wf_ord_lt_wf_ord_le_succ :
  forall alpha beta,
    alpha <wf beta ->
    succ alpha <wf= beta.
Proof.
intros.
unfold succ.
apply ord_lt_ord_le_succ.
assumption.
Qed.


Close Scope wf_ord_scope.
Close Scope ord_scope.
