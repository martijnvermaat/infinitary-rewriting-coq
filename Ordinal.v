(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines the type [ord] of tree ordinals.

   This formalisation of tree ordinals is based on notes by Peter Hancock:

     (Ordinal-theoretic) Proof Theory.
     Course notes from Midlands Graduate School, 2008.

     % \url{http://personal.cis.strath.ac.uk/~ph/} %
     # <a href="http://personal.cis.strath.ac.uk/~ph/">http://personal.cis.strath.ac.uk/~ph/</a> #

     % http://events.cs.bham.ac.uk/mgs2008/notes/proofTheory.pdf %
     # <a href="http://events.cs.bham.ac.uk/mgs2008/notes/proofTheory.pdf">http://events.cs.bham.ac.uk/mgs2008/notes/proofTheory.pdf</a> #

  See also the formalisation in Isabelle by Michael Compton:
  % http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html %
  # <a href="http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html">http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html</a> #
*)


Set Implicit Arguments.


Delimit Scope ord_scope with ord.
Open Scope ord_scope.


(** Inductive type for tree ordinals. *)
Inductive ord : Set :=
  | Zero  : ord
  | Succ  : ord -> ord
  | Limit : (nat -> ord) -> ord.

(** The intuition is that the [Limit] constructor represents the least
   upper bound of its argument sequence.

   We might like to exclude sequences such as (4,4,4,...), since they would
   not necessarily represent a limit ordinal. A way to do this is by
   imposing a monotonicity property on the [Limit] arguments. We first
   define an ordering on [ord] and, using that, define a subset of [ord]
   where the [Limit] arguments are monotone (in library [WfOrdinal]). *)

(** Type of predecessor indices of an ordinal. *)
Fixpoint pd_type (alpha : ord) : Set :=
  match alpha with
  | Zero       => False
  | Succ alpha => (unit + pd_type alpha) % type
  | Limit f    => { n : nat & pd_type (f n) }
  end.

Reserved Notation "alpha [ i ]" (at level 60).

(** Predecessor indices of an ordinal are essentially the paths on its tree
   structure starting from the root that cross at least one [Succ]
   constructor. *)

(** Predecessor of an ordinal for a given predecessor index. *)
Fixpoint pd (alpha : ord) : pd_type alpha -> ord :=
  match alpha with
  | Zero       => False_rect _
  | Succ alpha => fun i => match i with
                           | inl tt => alpha
                           | inr t  => alpha[t]
                           end
  | Limit f    => fun i => match i with
                           | existT _ n t => (f n)[t]
                           end
  end
where "alpha [ i ]" := (pd alpha i) : ord_scope.

(** [pd_type] and [pd] can be seen as defining a 'subtree' partial order on
   [ord]. We use it to define an extensional non-strict order on [ord]. *)

(** Non-strict order on [ord]. *)
Inductive ord_le : ord -> ord -> Prop :=
  | Ord_le_Zero  : forall beta,
                      Zero <= beta
  | Ord_le_Succ  : forall alpha beta i,
                      alpha <= beta[i] ->
                      Succ alpha <= beta
  | Ord_le_Limit : forall f beta,
                      (forall n, f n <= beta) ->
                      Limit f <= beta
where "alpha <= beta" := (ord_le alpha beta) : ord_scope.

(** Strict order on [ord]. *)
Definition ord_lt (alpha beta : ord) := exists i, alpha <= beta[i].
Infix " < " := ord_lt : ord_scope.

(** Equality on [ord]. *)
Definition ord_eq alpha beta := alpha <= beta /\ beta <= alpha.
Infix " == " := ord_eq (no associativity, at level 75) : ord_scope.

(** We proceed with some useful lemmas about these relations. *)

(** First predecessor of a successor is the original ordinal. *)
Lemma first_pd_after_succ_id :
  forall alpha, alpha = Succ alpha [inl (pd_type alpha) tt].
Proof.
trivial.
Qed.

(** No successor ordinal <= zero. *)
Lemma ord_le_not_succ_zero :
  forall alpha, ~ Succ alpha <= Zero.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
Qed.

(** No double successor <= 1. *)
Lemma ord_le_not_succ_succ_one :
  forall alpha, ~ Succ (Succ alpha) <= Succ Zero.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
destruct u.
apply (@ord_le_not_succ_zero alpha).
assumption.
assumption.
Qed.

(** If alpha <= zero, alpha <= any ordinal. *)
Lemma ord_le_zero_right :
  forall alpha beta,
    alpha <= Zero ->
    alpha <= beta.
Proof.
induction alpha as [| alpha _ | f IH]; intros beta H.
constructor.
inversion_clear H.
destruct i.
inversion_clear H.
constructor.
intro n.
apply IH.
trivial.
Qed.

(** If alpha <= a predecessor of beta, alpha <= beta. *)
Lemma ord_le_pd_right :
  forall alpha beta (i : pd_type beta),
    alpha <= beta[i] ->
    alpha <= beta.
Proof.
induction alpha as [| alpha IH | f IH]; intros beta i H.
constructor.
apply Ord_le_Succ with i.
inversion H as [| a b j |].
apply IH with j.
assumption.
constructor.
intro n.
inversion_clear H.
apply IH with i.
trivial.
Qed.

(** If alpha <= beta, all predecessors of alpha <= beta. *)
Lemma ord_le_pd_left :
  forall alpha beta (i : pd_type alpha),
    alpha <= beta ->
    alpha[i] <= beta.
Proof.
intros alpha beta i H.
induction H as [| alpha beta j H IH | f beta H IH].
destruct i.
destruct i as [[] | i']; apply ord_le_pd_right with j.
apply H.
apply IH.
destruct i.
apply IH.
Qed.

(** If alpha <= beta, alpha <= the successor of beta. *)
Lemma ord_le_succ_right :
  forall alpha beta,
    alpha <= beta ->
    alpha <= Succ beta.
Proof.
induction alpha as [| alpha _ | f IH]; intros beta H.
constructor.
inversion_clear H.
apply Ord_le_Succ with (inr unit i).
assumption.
constructor.
intro n.
apply IH.
inversion_clear H.
trivial.
Qed.

(** If the successor of alpha <= beta, alpha <= beta. *)
Lemma ord_le_succ_left :
  forall alpha beta,
    Succ alpha <= beta ->
    alpha <= beta.
Proof.
intros alpha beta H.
rewrite (first_pd_after_succ_id alpha).
apply ord_le_pd_left.
assumption.
Qed.

(** If the successor of alpha <= the successor of beta, alpha <= beta. *)
Lemma ord_le_succ_elim :
  forall alpha beta,
    Succ alpha <= Succ beta ->
    alpha <= beta.
Proof.
inversion_clear 1.
destruct i as [[] |]; [| apply ord_le_pd_right with p]; assumption.
Qed.

(** If the alpha <= beta, the successor of alpha <= the successor of beta. *)
Lemma ord_le_succ_intro :
  forall alpha beta,
    alpha <= beta ->
    Succ alpha <= Succ beta.
Proof.
intros.
apply Ord_le_Succ with (inl (pd_type beta) tt).
assumption.
Qed.

(** No successor of alpha is <= alpha. *)
Lemma ord_le_not_succ :
  forall alpha, ~ Succ alpha <= alpha.
Proof.
induction alpha as [| alpha IH | f IH]; intro H.
apply ord_le_not_succ_zero with Zero.
assumption.
apply IH.
exact (ord_le_succ_elim H).
inversion_clear H as [| a b i H' |].
inversion_clear H' as [| | a b H].
destruct i as [n i].
apply IH with n.
apply Ord_le_Succ with i.
apply H.
Qed.

(** If alpha <= a function value, alpha <= the limit of that function.
   Suggested by Bruno Barras. *)
Lemma ord_le_limit_right :
  forall alpha f n,
    alpha <= f n ->
    alpha <= Limit f.
Proof.
induction alpha as [| alpha _ | f IH]; intros g n H.
constructor.
inversion_clear H.
apply Ord_le_Succ with (existT (fun n => pd_type (g n)) n i).
assumption.
constructor.
intro m.
apply (IH m g n).
inversion_clear H.
trivial.
Qed.

(** If a limit <= alpha, any value value of the function <= alpha. *)
Lemma ord_le_limit_left :
  forall alpha f n,
    Limit f <= alpha ->
    f n <= alpha.
Proof.
intros alpha f n H.
inversion_clear H.
trivial.
Qed.

(** [<=] is reflexive. *)
Lemma ord_le_refl :
  forall alpha, alpha <= alpha.
Proof.
induction alpha as [| alpha IH | f IH].
constructor.
apply Ord_le_Succ with (inl (pd_type alpha) tt).
assumption.
constructor.
intro n.
apply ord_le_limit_right with n.
apply IH.
Qed.

(** [<=] is transitive. *)
Lemma ord_le_trans :
  forall alpha beta gamma,
    alpha <= beta ->
    beta <= gamma ->
    alpha <= gamma.
Proof.
intros alpha beta gamma H1.
revert gamma.
induction H1 as [| alpha beta i H IH | f beta H IH]; intros gamma H2.
constructor.
induction H2 as [| beta gamma j H' _ | f gamma H' IH'].
destruct i.
apply Ord_le_Succ with j.
apply IH.
destruct i as [[] | i']; simpl in * |- *.
assumption.
apply ord_le_pd_left.
assumption.
destruct i as [n i]; simpl in * |- *.
apply (IH' n i H IH).
constructor.
intro n.
exact (IH n gamma H2).
Qed.

(** [<=] is antisymmetric (for [==]). *)
Lemma ord_le_antisymm :
  forall alpha beta,
    alpha <= beta ->
    beta <= alpha ->
    alpha == beta.
Proof.
intros.
unfold ord_eq.
split; assumption.
Qed.

(* TODO: Can we prove <= is total? *)

(** [==] is reflexive. *)
Lemma ord_eq_refl :
  forall alpha, alpha == alpha.
Proof.
split; apply ord_le_refl.
Qed.

(** [==] is symmetric. *)
Lemma ord_eq_symm :
  forall alpha beta,
    alpha == beta ->
    beta == alpha.
Proof.
split; apply H.
Qed.

(** [==] is transitive. *)
Lemma ord_eq_trans :
  forall alpha beta gamma,
    alpha == beta ->
    beta == gamma ->
    alpha == gamma.
Proof.
destruct 1.
destruct 1.
split; apply ord_le_trans with beta; assumption.
Qed.

(** Not zero < zero. *)
Lemma ord_lt_zero_zero :
  ~ Zero < Zero.
Proof.
intro H.
destruct H as [i H].
elim i.
Qed.

(** If alpha <= beta, not beta <= a predecessor of alpha. *)
Lemma ord_le_not_pd_right :
  forall alpha beta i,
    alpha <= beta ->
    ~ beta <= alpha[i].
Proof.
induction alpha as [| alpha IH | f IH]; intros beta i H1 H2.
destruct i.
destruct i.
destruct u.
apply ord_le_not_succ with alpha.
apply ord_le_trans with beta; assumption.
exact (IH beta p (ord_le_succ_left H1) H2).
destruct i.
inversion_clear H1.
exact (IH x beta p (H x) H2).
Qed.

(** Not alpha <= a predecessor of alpha. *)
Lemma ord_le_not_pd_right_weak :
  forall alpha i, ~ alpha <= alpha[i].
Proof.
intros.
apply ord_le_not_pd_right.
apply ord_le_refl.
Qed.


(** [<] is transitive. *)
Lemma ord_lt_trans :
  forall alpha beta gamma,
    alpha < beta ->
    beta < gamma ->
    alpha < gamma.
Proof.
intros alpha beta gamma.
destruct 1 as [i].
destruct 1 as [j].
exists j.
apply ord_le_trans with beta; [apply ord_le_pd_right with i |]; assumption.
Qed.

(** [<] is irreflexive. *)
Lemma ord_lt_irrefl :
  forall alpha, ~ alpha < alpha.
Proof.
intros alpha H.
destruct H as [i H].
exact (ord_le_not_pd_right_weak i H).
Qed.

(** [<] is asymmetric. *)
Lemma ord_lt_asymm :
  forall alpha beta,
    alpha < beta ->
    ~ beta < alpha.
Proof.
intros alpha beta H1 H2.
destruct H1 as [i H1].
destruct H2 as [j H2].
apply (@ord_le_not_pd_right alpha beta j);
  [apply ord_le_pd_right with i |]; assumption.
Qed.

(** [pd_type] is closed under transitivity. *)
Lemma pd_trans :
  forall alpha i j,
    exists k, pd alpha k = pd (pd alpha i) j.
Proof.
induction alpha as [| alpha IH | f IH]; intros.
elim i.
destruct i as [[] | i]; simpl in j |- *.
exists (inr _ j).
reflexivity.
destruct (IH i j) as [k H].
exists (inr _ k).
assumption.
destruct i as [n i]; simpl in j |- *.
destruct (IH n i j) as [k H].
exists (existT (fun n => pd_type (f n)) n k).
assumption.
Qed.

(** If the successor of alpha < beta, alpha < beta. *)
Lemma ord_lt_succ_left :
  forall alpha beta,
    Succ alpha < beta ->
    alpha < beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
exists i.
apply ord_le_succ_left.
assumption.
Qed.

(** If alpha < beta, alpha < the successor of beta. *)
Lemma ord_lt_succ_right :
  forall alpha beta,
    alpha < beta ->
    alpha < Succ beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
exists (inl (pd_type beta) tt).
apply ord_le_pd_right with i.
assumption.
Qed.

(** If alpha < beta, alpha <= beta. *)
Lemma ord_lt_ord_le :
  forall alpha beta, alpha < beta -> alpha <= beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
apply ord_le_pd_right with i.
assumption.
Qed.

(** If alpha < beta, the successor of alpha <= beta. *)
Lemma ord_lt_ord_le_succ :
  forall alpha beta,
    alpha < beta ->
    Succ alpha <= beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
apply Ord_le_Succ with i.
assumption.
Qed.

(** If alpha < beta, not beta <= alpha. *)
Lemma ord_lt_not_ord_le :
  forall alpha beta,
    alpha < beta ->
    ~ beta <= alpha.
Proof.
intros alpha beta H1 H2.
destruct H1 as [i H1].
apply (@ord_le_not_pd_right beta alpha i); assumption.
Qed.

(** If alpha <= a predecessor of the successor of beta, alpha <= beta. *)
Lemma ord_le_succ_pd_right :
  forall alpha beta i,
    alpha <= Succ beta [i] ->
    alpha <= beta.
Proof.
(* This is a messy proof *)
induction alpha; intros.
simpl in H.
destruct i.
destruct u.
assumption.
apply Ord_le_Zero.
destruct beta.
destruct i.
destruct u.
destruct (ord_le_not_succ_zero H).
destruct p.
apply Ord_le_Succ with (inl (pd_type beta) tt).
simpl.
simpl in H.
destruct i.
destruct u.
apply ord_le_succ_elim.
assumption.
destruct p.
apply ord_le_succ_left.
destruct u.
assumption.
apply ord_le_succ_left.
apply ord_le_pd_right with p.
assumption.
simpl in H.
destruct i.
destruct u.
assumption.
destruct p.
apply ord_le_limit_right with x.
apply ord_le_pd_right with p.
assumption.
apply Ord_le_Limit.
intro.
inversion_clear H0.
apply H with i.
apply H1.
Qed.

(** Ordinal arithmetic. *)

Fixpoint add (alpha beta : ord) : ord :=
  match beta with
  | Zero      => alpha
  | Succ beta => Succ (add alpha beta)
  | Limit f   => Limit (fun o => add alpha (f o))
  end.

Fixpoint mul (alpha beta : ord) : ord :=
  match beta with
  | Zero      => Zero
  | Succ beta => add (mul alpha beta) alpha
  | Limit f   => Limit (fun o => mul alpha (f o))
  end.

Fixpoint exp (alpha beta : ord) : ord :=
  match beta with
  | Zero      => Succ Zero
  | Succ beta => mul (exp alpha beta) alpha
  | Limit f   => Limit (fun o => exp alpha (f o))
  end.

Lemma ord_le_add_right :
  forall alpha beta,
    alpha <= add alpha beta.
Proof.
intros alpha beta.
induction beta as [| beta IH | f IH].
apply ord_le_refl.
apply ord_le_succ_right.
exact IH.
apply ord_le_limit_right with 0.
apply IH.
Qed.

Lemma ord_le_add :
  forall alpha beta gamma,
    beta <= gamma ->
    add alpha beta <= add alpha gamma.
Proof.
intros alpha beta gamma H.
induction H as [gamma | beta gamma i H IH | f gamma H IH].
apply ord_le_add_right.
induction gamma as [| gamma IHg | f IHg]; simpl.
elim i.
destruct i as [[] | i].
apply Ord_le_Succ with (inl (pd_type (add alpha gamma)) tt).
apply IH.
apply ord_le_succ_right.
apply IHg with i; assumption.
destruct i as [n i].
apply ord_le_limit_right with n.
apply IHg with i; assumption.
constructor.
intro n.
apply IH.
Qed.

Lemma ord_lt_add :
  forall alpha beta gamma,
    beta < gamma ->
    add alpha beta < add alpha gamma.
Proof.
intros alpha beta gamma H.
unfold ord_lt; destruct H as [i H].
induction gamma as [| gamma _ | f IH]; simpl.
destruct i.
exists (inl _ tt); simpl.
apply ord_le_add.
destruct i as [[] | i].
assumption.
apply ord_le_pd_right with i.
assumption.
destruct i as [n i].
specialize IH with n i.
destruct IH as [j IH].
assumption.
exists (existT (fun n => pd_type (add alpha (f n))) n j).
assumption.
Qed.

(** The natural numbers can be coerced into finite ordinals. *)

Fixpoint nat_as_ord (n : nat) : ord :=
  match n with
  | O   => Zero
  | S n => Succ (nat_as_ord n)
  end.

Coercion nat_as_ord : nat >-> ord.

(** The smallest infinite ordinal is the limit of the natural numbers. *)
Definition omega := Limit (fun n => n).

(** We show that [<=] and [<] on ordinals are the same as [<=] and [<] on
   natural numbers. *)

Require Import Le.

Lemma le_implies_ord_le : forall n m, (n <= m)%nat -> n <= m.
Proof.
induction n as [| n IH]; intros m H.
constructor.
destruct m as [| m].
contradiction le_Sn_0 with n.
apply ord_le_succ_intro.
apply IH.
apply le_S_n.
assumption.
Qed.

Lemma ord_le_implies_le : forall (n m : nat), n <= m -> (n <= m)%nat.
Proof.
induction n as [| n IH]; intros m H.
apply le_0_n.
destruct m as [| m].
contradiction ord_le_not_succ_zero with n.
apply le_n_S.
apply IH.
apply ord_le_succ_elim.
assumption.
Qed.

Lemma ord_le_le : forall n m, (n <= m)%nat <-> n <= m.
Proof.
split.
apply le_implies_ord_le.
apply ord_le_implies_le.
Qed.

Require Import Lt.

Lemma lt_implies_ord_lt : forall n m, (n < m)%nat -> n < m.
Proof.
induction n as [| n IH]; intros m H.
destruct H; exists (inl _ tt); constructor.
destruct m as [| m].
contradiction lt_n_O with (S n).
exists (inl _ tt).
apply ord_lt_ord_le_succ; simpl.
apply IH.
apply lt_S_n.
assumption.
Qed.

Lemma ord_lt_implies_lt : forall (n m : nat), n < m -> (n < m)%nat.
Proof.
induction n as [| n IH]; intros m H.
destruct H as [i H].
destruct m as [| m].
elim i.
apply lt_0_Sn.
destruct H as [i H].
destruct m as [| m].
elim i.
apply lt_n_S.
apply IH.
(* this can be cleaned up *)
destruct m as [| m].
destruct i as [[] | []].
contradiction ord_le_not_succ_zero with n.
exists (inl _ tt).
destruct i as [[] | [[] | i]].
apply ord_le_succ_elim.
assumption.
apply ord_le_succ_left.
assumption.
apply ord_le_succ_left.
apply ord_le_pd_right with i.
assumption.
Qed.

Lemma ord_lt_lt : forall n m, (n < m)%nat <-> n < m.
Proof.
split.
apply lt_implies_ord_lt.
apply ord_lt_implies_lt.
Qed.

(** We now prove two simple facts about our equality [==] containing
   different representations of omega. *)

Lemma fact_a :
  Limit (fun n => S n) == omega.
Proof.
split; constructor; intro n.
apply Ord_le_Succ with (existT (fun n:nat => pd_type n) (S n) (inl _ tt)).
apply ord_le_refl.
destruct n as [| n].
constructor.
apply Ord_le_Succ with (existT (fun n:nat => pd_type (S n)) n (inl _ tt)).
apply ord_le_refl.
Qed.

Lemma fact_b :
  Limit (fun n => n * 2) == omega.
Proof.
split; constructor; intro n.
destruct n as [| n]; simpl.
constructor.
apply Ord_le_Succ with (existT (fun n:nat => pd_type n) (S (S (n * 2))) (inl _ tt)).
apply ord_le_refl.
destruct n as [| n].
constructor.
apply Ord_le_Succ with (existT (fun n:nat => pd_type (n * 2)) (S n) (inl _ tt)).
simpl.
induction n as [| n IH]; simpl.
constructor.
apply ord_le_succ_right.
apply ord_le_succ_intro.
exact IH.
Qed.

(** A weak inversion property of ordinals equal to omega. *)
Lemma ord_eq_omega_discriminate :
  forall alpha,
    alpha == omega ->
    exists f, alpha = Limit f.
Proof.
intros [| alpha | f] [H1 H2].
inversion_clear H2.
contradict (ord_le_not_succ_zero (H 1)).
inversion_clear H1.
inversion_clear H2.
destruct i as [n i].
contradict (ord_le_not_pd_right i (ord_le_succ_elim (H0 (S n))) H).
exists f; reflexivity.
Qed.


Close Scope ord_scope.
