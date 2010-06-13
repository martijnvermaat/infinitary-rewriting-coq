(*
  Formalisation of tree ordinals based on the notes:

    Peter Hancock, "Ordinal theoretic proof theory"

  http://personal.cis.strath.ac.uk/~ph/

  See also the formalisation in Isabelle by Michael Compton:
  http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html
*)

(*
Definition fam (A : Type) : Type := { I : Set & I -> A }.
Definition pow (A : Type) : Type := A -> Set.

Definition zero z := pred_type z -> False.

Definition pd (alpha : ord) : fam ord := existT _ (pred_type alpha) (pred alpha).
*)


Set Implicit Arguments.


Delimit Scope ord_scope with ord.
Open Scope ord_scope.


Inductive ord : Set :=
  | Zero  : ord
  | Succ  : ord -> ord
  | Limit : (nat -> ord) -> ord.

Fixpoint pred_type (alpha : ord) : Set :=
  match alpha with
  | Zero       => False
  | Succ alpha => (unit + pred_type alpha) % type
  | Limit f    => { n : nat & pred_type (f n) }
  end.

Reserved Notation "alpha [ i ]" (at level 60).

Fixpoint pred (alpha : ord) : pred_type alpha -> ord :=
  match alpha with
  | Zero       => False_rect _
  | Succ alpha => fun i => match i with
                           | inl tt => alpha
                           | inr t  => alpha[t]
                           end
  | Limit f    => fun i => match i with
                           | existT n t => (f n)[t]
                           end
  end
where "alpha [ i ]" := (pred alpha i) : ord_scope.

Inductive ord_le : ord -> ord -> Prop :=
  | Ord_le_Zero  : forall alpha,
                      Zero <= alpha
  | Ord_le_Succ  : forall alpha beta i,
                      alpha <= beta[i] ->
                      Succ alpha <= beta
  | Ord_le_Limit : forall f beta,
                      (forall n, f n <= beta) ->
                      Limit f <= beta
where "alpha <= beta" := (ord_le alpha beta) : ord_scope.

(*Definition ord_lt (alpha beta : ord) := { t : pred_type beta & ord_le alpha (pred beta t) }.*)
(*Definition ord_lt alpha beta := alpha <= beta /\ ~ beta <= alpha.*)
Definition ord_lt (alpha beta : ord) := exists i, alpha <= beta[i].
Infix " < " := ord_lt : ord_scope.

(* Should we use this as our ordinal equality? Then <= is trivially
   antisymmetric, while it is not for structural equality.
   (I think this is fixed though, if we impose the increasing restriction
   of the limit functions) *)
Definition ord_eq alpha beta := alpha <= beta /\ beta <= alpha.
Infix " == " := ord_eq (no associativity, at level 75) : ord_scope.

(* First predecessor of a successor is the original ordinal. *)
Lemma first_pred_after_succ_id :
  forall alpha, alpha = Succ alpha [inl (pred_type alpha) tt].
Proof.
trivial.
Qed.

(* No successor ordinal <= zero *)
Lemma ord_le_not_succ_zero :
  forall alpha, ~ Succ alpha <= Zero.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
Qed.

(* No double successor <= 1 *)
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

(* If alpha <= zero, alpha <= any ordinal *)
Lemma ord_le_zero_all :
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

(* If alpha <= a predecessor of beta, alpha <= beta *)
Lemma ord_le_pred_right :
  forall alpha beta (i : pred_type beta),
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

(* If alpha <= beta, all predecessors of alpha <= beta *)
Lemma ord_le_pred_left :
  forall alpha beta (i : pred_type alpha),
    alpha <= beta ->
    alpha[i] <= beta.
Proof.
intros alpha beta i H.
induction H as [| alpha beta j H IH | f beta H IH].
destruct i.
destruct i as [[] | i']; apply ord_le_pred_right with j.
apply H.
apply IH.
destruct i.
apply IH.
Qed.

(* If alpha <= beta, alpha <= the successor of beta *)
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

(* If the successor of alpha <= beta, alpha <= beta *)
Lemma ord_le_succ_left :
  forall alpha beta,
    Succ alpha <= beta ->
    alpha <= beta.
Proof.
intros alpha beta H.
rewrite (first_pred_after_succ_id alpha).
apply ord_le_pred_left.
assumption.
Qed.

(* If the successor of alpha <= the successor of beta, alpha <= beta *)
Lemma ord_le_succ_elim :
  forall alpha beta,
    Succ alpha <= Succ beta ->
    alpha <= beta.
Proof.
inversion_clear 1.
destruct i as [[] |]; [| apply ord_le_pred_right with p]; assumption.
Qed.

(* If the alpha <= beta, the successor of alpha <= the successor of beta *)
Lemma ord_le_succ_intro :
  forall alpha beta,
    alpha <= beta ->
    Succ alpha <= Succ beta.
Proof.
intros.
apply Ord_le_Succ with (inl (pred_type beta) tt).
assumption.
Qed.

(* No successor of alpha is <= alpha *)
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

(* Suggested by Bruno Barras *)
(* If alpha <= a function value, alpha <= the limit of that function *)
Lemma ord_le_limit_right :
  forall alpha f n,
    alpha <= f n ->
    alpha <= Limit f.
Proof.
induction alpha as [| alpha _ | f IH]; intros g n H.
constructor.
inversion_clear H.
apply Ord_le_Succ with (existT (fun n => pred_type (g n)) n i).
assumption.
constructor.
intro m.
apply (IH m g n).
inversion_clear H.
trivial.
Qed.

(* If a limit <= alpha, any value value of the function <= alpha *)
Lemma ord_le_limit_left :
  forall alpha f n,
    Limit f <= alpha ->
    f n <= alpha.
Proof.
intros alpha f n H.
inversion_clear H.
trivial.
Qed.

(* <= is reflexive *)
Lemma ord_le_refl :
  forall alpha, alpha <= alpha.
Proof.
induction alpha as [| alpha IH | f IH].
constructor.
apply Ord_le_Succ with (inl (pred_type alpha) tt).
assumption.
constructor.
intro n.
apply ord_le_limit_right with n.
apply IH.
Qed.

(* <= is transitive *)
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
apply ord_le_pred_left.
assumption.
destruct i as [n i]; simpl in * |- *.
apply (IH' n i H IH).
constructor.
intro n.
exact (IH n gamma H2).
Qed.

(* We cannot prove this for = *)
(* <= is antisymmetric *)
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

(* == is reflexive *)
Lemma ord_eq_refl :
  forall alpha, alpha == alpha.
Proof.
split; apply ord_le_refl.
Qed.

(* == is symmetric *)
Lemma ord_eq_symm :
  forall alpha beta,
    alpha == beta ->
    beta == alpha.
Proof.
split; apply H.
Qed.

(* == is transitive *)
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

(* < is transitive *)
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
apply ord_le_trans with beta; [apply ord_le_pred_right with i |]; assumption.
Qed.

(* TODO: find appropriate place for this lemma *)
Lemma ord_lt_zero_zero :
  ~ Zero < Zero.
Proof.
intro H.
destruct H as [i H].
elim i.
Qed.

(* TODO: move this lemma to a better place *)
Lemma ord_le_not_pred_right_strong :
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

(* TODO: move this lemma too *)
Lemma ord_le_not_pred_right :
  forall alpha i, ~ alpha <= alpha[i].
Proof.
intros.
apply ord_le_not_pred_right_strong.
apply ord_le_refl.
Qed.

(* < is irreflexive *)
Lemma ord_lt_irrefl :
  forall alpha, ~ alpha < alpha.
Proof.
intros alpha H.
destruct H as [i H].
exact (ord_le_not_pred_right i H).
Qed.

(* < is asymmetric *)
Lemma ord_lt_asymm :
  forall alpha beta,
    alpha < beta ->
    ~ beta < alpha.
Proof.
intros alpha beta H1 H2.
destruct H1 as [i H1].
destruct H2 as [j H2].
apply (@ord_le_not_pred_right_strong alpha beta j);
  [apply ord_le_pred_right with i |]; assumption.
Qed.

(* If the successor of alpha < beta, alpha < beta *)
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

(* If alpha < beta, alpha < the successor of beta *)
Lemma ord_lt_succ_right :
  forall alpha beta,
    alpha < beta ->
    alpha < Succ beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
exists (inl (pred_type beta) tt).
apply ord_le_pred_right with i.
assumption.
Qed.

(* If alpha < beta, alpha <= beta *)
Lemma ord_lt_ord_le :
  forall alpha beta, alpha < beta -> alpha <= beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
apply ord_le_pred_right with i.
assumption.
Qed.

(* If alpha < beta, the successor of alpha <= beta *)
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

(* TODO: move *)
Lemma ord_lt_pred_right :
  forall alpha beta (i : pred_type beta),
    alpha < beta[i] ->
    alpha < beta.
Proof.
(* TODO *)
Admitted.

Lemma ord_lt_not_ord_le :
  forall alpha beta,
    alpha < beta ->
    ~ beta <= alpha.
Proof.
intros alpha beta H1 H2.
destruct H1 as [i H1].
apply (@ord_le_not_pred_right_strong beta alpha i); assumption.
Qed.

(* TODO: this needs cleanup *)
Lemma sdfsdf :
  forall alpha beta i,
    alpha <= Succ beta [i] ->
    alpha <= beta.
Proof.
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
apply Ord_le_Succ with (inl (pred_type beta) tt).
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
apply ord_le_pred_right with p.
assumption.
simpl in H.
destruct i.
destruct u.
assumption.
destruct p.
apply ord_le_limit_right with x.
apply ord_le_pred_right with p.
assumption.
apply Ord_le_Limit.
intro.
inversion_clear H0.
apply H with i.
apply H1.
Qed.

(* If alpha < beta and beta <= gamma, alpha < gamma *)
(* TODO: variations and move to appropriate place *)
Lemma ord_lt_trans_ord_le_right :
  forall alpha beta gamma,
    alpha < beta ->
    beta <= gamma ->
    alpha < gamma.
Proof.
intros.
destruct H.
destruct gamma.
assert (H1 := ord_le_zero_all (beta[x]) H0).
destruct (ord_le_not_pred_right x H1).
destruct H0.
destruct x.
exists i.
apply ord_le_trans with alpha0.
simpl in H.
apply sdfsdf with x.
assumption.
assumption.
(* TODO: we need this *)
Admitted.

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

(* Image of naturals in pre-ordinals *)
Fixpoint nat_as_ord (n : nat) : ord :=
  match n with
  | O   => Zero
  | S n => Succ (nat_as_ord n)
  end.

Coercion nat_as_ord : nat >-> ord.

Definition omega := Limit (fun n => n).

Lemma lt_nat_ord : forall n m, (n < m)%nat -> n < m.
Proof.
(* TODO: see old proof below *)
Admitted.

Lemma lt_ord_nat : forall (n m : nat), n < m -> (n < m)%nat.
Proof.
(* TODO: see old proof below *)
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

Lemma aaaa :
  Limit (fun n => S n) == Limit (fun n => n).
Proof.
split; constructor; intro n.
apply Ord_le_Succ with (existT (fun n:nat => pred_type n) (S n) (inl _ tt)).
apply ord_le_refl.
destruct n as [| n].
constructor.
apply Ord_le_Succ with (existT (fun n:nat => pred_type (S n)) n (inl _ tt)).
apply ord_le_refl.
Qed.

Lemma bbbb :
  Limit (fun n => n * 2) == Limit (fun n => n).
Proof.
split; constructor; intro n.
destruct n as [| n]; simpl.
constructor.
apply Ord_le_Succ with (existT (fun n:nat => pred_type n) (S (S (n * 2))) (inl _ tt)).
apply ord_le_refl.
destruct n as [| n].
constructor.
apply Ord_le_Succ with (existT (fun n:nat => pred_type (n * 2)) (S n) (inl _ tt)).
simpl.
induction n as [| n IH]; simpl.
constructor.
apply ord_le_succ_right.
apply ord_le_succ_intro.
exact IH.
Qed.

Lemma ord_le_omega_elim :
  forall alpha,
    alpha <= omega ->
    alpha < omega \/ alpha == omega.
Proof.
intros alpha H. unfold ord_lt.
induction alpha as [| alpha IH | f IH].
left.
exists (existT (fun (n:nat) => pred_type n) 1 (inl _ tt)).
constructor.
left.
destruct IH as [[[n j] H1] | H1].
apply (ord_le_succ_left H).
simpl in H1.
exists (existT (fun (n:nat) => pred_type n) (S n) (inl _ tt)); simpl.
destruct n as [| n].
elim j.
destruct j as [[] | j]; simpl in H1; apply ord_le_succ_intro.
assumption.
apply ord_le_pred_right with j.
assumption.
contradiction ord_le_not_pred_right_strong with (Succ alpha) omega (inl (pred_type alpha) tt).
apply H1.
right.
split.
assumption.
constructor.
(* TODO: monotonicity of f assumed *)
assert (G : forall n m, (n < m)%nat -> f n < f m).
admit.
(* TODO: cleanup, below is a mess *)
induction n as [| n IHn]; simpl.
constructor.
assert (J := G n (S n)).
destruct J as [i J].
auto.
apply Ord_le_Succ with (existT (fun (n:nat) => pred_type (f n)) (S n) i).
simpl.
apply ord_le_trans with (f n).
induction n as [| n IHnn]; simpl.
constructor.
assert (K := G n (S n)).
destruct K as [k K].
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

(* TODO: can we strengthen this, say, to f:nat->nat ? *)
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
contradict (ord_le_not_pred_right_strong
  i (ord_le_succ_elim (H0 (S n))) H).
exists f; reflexivity.
Qed.


Close Scope ord_scope.
