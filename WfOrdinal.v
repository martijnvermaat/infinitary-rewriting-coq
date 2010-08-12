(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines the type [wf_ord] of well-formed tree ordinals.

   The well-formed tree ordinals are a subset of [ord] (defined in the
   [Ordinal] library) where we restrict the arguments of [Limit] constructors
   to be monotone. *)


Require Export Ordinal.


Set Implicit Arguments.


Delimit Scope wf_ord_scope with wf_ord.
Open Scope ord_scope.
Open Scope wf_ord_scope.


(** Well-formed ordinals are those whose the limit functions are monotone. *)
Fixpoint wf alpha : Prop :=
  match alpha with
  | Zero      => True
  | Succ beta => wf beta
  | Limit f   => forall n, wf (f n) /\ forall m, (n < m)%nat -> f n < f m
  end.

(** Addition of well-formed ordinals yields a well-formed ordinal. *)
Lemma add_wf :
  forall alpha beta,
    wf alpha ->
    wf beta ->
    wf (add alpha beta).
Proof.
intros alpha beta.
revert beta.
induction beta as [| beta IH | f IH]; intros WFa WFb.
assumption.
apply IH; assumption.
intro n.
split.
apply IH.
assumption.
apply WFb.
intros m H.
apply ord_lt_add.
apply WFb.
assumption.
Qed.

(** All natural numbers are well-formed. *)
Lemma nat_wf :
  forall (n : nat), wf n.
Proof.
induction n.
exact I.
assumption.
Qed.

(** We now define the well-formed ordinals [wf_ord] as a subset of the
   ordinals [ord] by the [wf] condition. *)

Definition wf_ord : Set := sig wf.

(** Image of well-formed ordinals in ordinals. *)

Definition wf_ord_as_ord (alpha : wf_ord) : ord :=
  proj1_sig alpha.

Coercion wf_ord_as_ord : wf_ord >-> ord.

(** For any well-formed alpha <= zero, alpha = zero.

   (We would like to leave out the explicit coercion in the statement of
   this lemma.) *)
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

(** Definitions of well-formed ordinals. *)

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

(** We lift the [<=], [<], and [==] relations to [wf_ord]. *)

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

(** The image of the natural numbers in the ordinals can of course be
   lifted to well-formed ordinals. *)

Definition nat_as_wf_ord (n : nat) : wf_ord :=
  exist wf n (nat_wf n).

Coercion nat_as_wf_ord : nat >-> wf_ord.

(** A well-formed definition of omega with a proof that it is really greater
   than all natural numbers. *)

Definition wf_omega := limit nat_as_wf_ord lt_implies_ord_lt.

Lemma n_le_omega : forall (n : nat), n <wf= wf_omega.
Proof.
destruct n as [| n]; unfold wf_ord_le; simpl.
constructor.
apply Ord_le_Succ with (i := existT (fun (n:nat) => pd_type n) (S n) (inl (pd_type n) tt)).
apply ord_le_refl.
Qed.

Lemma n_lt_omega : forall (n : nat), n <wf wf_omega.
Proof.
intro n.
exists (existT (fun (n:nat) => pd_type n) (S n) (inl (pd_type n) tt)).
apply ord_le_refl.
Qed.

(** Some inversion lemma for alpha <= omega. *)
Lemma ord_le_omega_elim :
  forall alpha,
    alpha <wf= wf_omega ->
    alpha <wf wf_omega \/ alpha =wf= wf_omega.
Proof.
intros alpha H. unfold wf_ord_lt.
destruct alpha as [alpha wf_alpha].
induction alpha as [| alpha IH | f IH].
left.
exists (existT (fun (n:nat) => pd_type n) 1 (inl _ tt)).
constructor.
left.
destruct IH with wf_alpha as [[[n j] H1] | H1].
apply (ord_le_succ_left H).
simpl in H1.
exists (existT (fun (n:nat) => pd_type n) (S n) (inl _ tt)); simpl.
destruct n as [| n].
elim j.
destruct j as [[] | j]; simpl in H1; apply ord_le_succ_intro.
assumption.
apply ord_le_pd_right with j.
assumption.
contradiction ord_le_not_pd_right with (Succ alpha) omega (inl (pd_type alpha) tt).
apply H1.
right.
split.
assumption.
simpl.
constructor.
(* TODO: cleanup, below is a mess *)
induction n as [| n IHn]; simpl.
constructor.
destruct wf_alpha with n as [_ G].
destruct G with (S n) as [i J]; clear G.
auto.
apply Ord_le_Succ with (existT (fun (n:nat) => pd_type (f n)) (S n) i).
simpl.
apply ord_le_trans with (f n).
induction n as [| n IHnn]; simpl.
constructor.
destruct wf_alpha with n as [_ G].
destruct G with (S n) as [k K]; clear G.
auto.
apply Ord_le_Succ with k.
apply ord_le_trans with (f n).
apply IHnn with k.
apply ord_le_succ_left.
assumption.
assumption.
assumption.
assumption.
Qed.


Close Scope wf_ord_scope.
Close Scope ord_scope.
