(*
  Formalisation of tree ordinals based on the notes:

    Peter Hancock, "Ordinal theoretic proof theory"

  See also the formalisation in Isabelle by Michael Compton:
  http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html
*)

(*
Definition fam (A : Type) : Type := { I : Set & I -> A }.
Definition pow (A : Type) : Type := A -> Set.

Definition zero z := pred_type z -> False.

Definition pd (alpha : ord) : fam ord := existT _ (pred_type alpha) (pred alpha).
*)

Delimit Scope ord_scope with ord.

Open Scope ord_scope.

Inductive ord : Set :=
  | Zero  : ord
  | Succ  : ord -> ord
  | Limit : (nat -> ord) -> ord.

(* Image of naturals in ordinals *)
Fixpoint nat_as_ord (n : nat) : ord :=
  match n with
  | O   => Zero
  | S n => Succ (nat_as_ord n)
  end.

Coercion nat_as_ord : nat >-> ord.

Fixpoint pred_type (alpha : ord) : Set :=
  match alpha with
  | Zero       => False
  | Succ alpha => (unit + pred_type alpha) % type
  | Limit f    => { n : nat & pred_type (f n) }
  end.

Notation "!" := (False_rect _).

Fixpoint pred (alpha : ord) : pred_type alpha -> ord :=
  match alpha with
  | Zero       => !
  | Succ alpha => fun i => match i with
                           | inl tt => alpha
                           | inr t  => pred alpha t
                           end
  | Limit f    => fun i => match i with
                           | existT n t => pred (f n) t
                           end
  end.

Inductive ord_le : ord -> ord -> Prop :=
  | Ord_le_Zero  : forall alpha,
                     Zero <= alpha
  | Ord_le_Succ  : forall alpha beta i,
                     alpha <= pred beta i ->
                     Succ alpha <= beta
  | Ord_le_Limit : forall f beta,
                     (forall n, f n <= beta) ->
                     Limit f <= beta
where "alpha <= beta" := (ord_le alpha beta) : ord_scope.

(* TODO: Why not  alpha < beta  <=>  alpha <= beta /\ ~ beta <= alpha  ? *)
(*Definition ord_lt (alpha beta : ord) := { t : pred_type beta & ord_le alpha (pred beta t) }.*)
(*Definition ord_lt (alpha beta : ord) := exists i, ord_le alpha (pred beta i).*)
Definition ord_lt alpha beta := alpha <= beta /\ ~ beta <= alpha.
Infix " < " := ord_lt : ord_scope.

(* Should we use this as our ordinal equality? Then <= is trivially
   antisymmetric, while it is not for structural equality.
   (I think this is fixed though, if we impose the increasing restriction
   of the limit functions) *)
Definition ord_eq alpha beta := alpha <= beta /\ beta <= alpha.
Infix " == " := ord_eq (no associativity, at level 75) : ord_scope.

(* First predecessor of a successor is the original ordinal. *)
Lemma first_pred_after_succ_id :
  forall alpha, alpha = pred (Succ alpha) (inl (pred_type alpha) tt).
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
apply (ord_le_not_succ_zero alpha).
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
    alpha <= pred beta i ->
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
    pred alpha i <= beta.
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
apply Ord_le_Succ with (i := inr unit i).
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
Lemma ord_le_succ :
  forall alpha beta,
    Succ alpha <= Succ beta ->
    alpha <= beta.
Proof.
inversion_clear 1.
destruct i as [[] |]; [| apply ord_le_pred_right with p]; assumption.
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
apply Ord_le_Succ with (i := existT (fun n => pred_type (g n)) n i).
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
Admitted.

(* <= is reflexive *)
Lemma ord_le_refl :
  forall alpha, alpha <= alpha.
Proof.
induction alpha as [| alpha IH | f IH].
constructor.
apply Ord_le_Succ with (i := inl (pred_type alpha) tt).
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
unfold ord_lt.
intros alpha beta gamma H1 H2.
split.
apply ord_le_trans with beta.
apply H1.
apply H2.
intro H.
apply H2.
apply ord_le_trans with alpha.
assumption.
apply H1.
Qed.

(* < is irreflexive *)
Lemma ord_lt_irrefl :
  forall alpha, ~ alpha < alpha.
Proof.
intros alpha H.
destruct H.
contradiction.
Qed.

(* < is asymmetric *)
Lemma ord_lt_asymm :
  forall alpha beta,
    alpha < beta ->
    ~ beta < alpha.
Proof.
intros alpha beta H1 H2.
destruct H1.
destruct H2.
contradiction.
Qed.

(* If the successor of alpha < beta, alpha < beta *)
Lemma ord_lt_succ_left :
  forall alpha beta,
    Succ alpha < beta ->
    alpha < beta.
Proof.
intros alpha beta H.
destruct H as [H1 H2].
split; rewrite (first_pred_after_succ_id alpha).
apply ord_le_pred_left.
assumption.
intro H.
apply H2.
apply ord_le_succ_right.
assumption.
Qed.

(*
   Below we try to seperate the good from the bad
*)

(* Good ordinals are those where the limit functions are increasing *)
Fixpoint good alpha : Prop :=
  match alpha with
  | Zero      => True
  | Succ beta => good beta
  | Limit f   => forall n, good (f n) /\ forall m, (n < m)%nat -> (f n) < (f m)
  end.

Lemma ord_le_zero_zero :
  Zero < Zero -> False.
Proof.
destruct 1.
contradiction.
Qed.

(* Needed for rewrite ... at occurrence *)
Require Import Setoid.

(* For any good alpha <= zero, alpha = zero *)
Lemma ord_le_zero_good :
  forall alpha,
    good alpha ->
    alpha <= Zero ->
    alpha = Zero.
Proof.
induction alpha as [| alpha _ | f IH]; intros G H.
reflexivity.
elim (ord_le_not_succ_zero alpha H).
elimtype False.
apply ord_le_zero_zero.
simpl in G.
destruct (G 1) as [G1 Gnm].
destruct (G 2) as [G2 _].
inversion_clear H.
rewrite <- (IH 1) at 1.
rewrite <- (IH 2).
apply Gnm.
constructor.
assumption.
apply H0.
assumption.
apply H0.
Qed.

(* < on nat is the same as < on ord *)
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

(* TODO: I think proofs like the above would benefit from adding
   some lemma's about ord_le as hints *)

Definition omega := Limit id.

Lemma n_le_omega : forall (n : nat), n <= omega.
Proof.
induction n as [| n IH]; simpl; unfold omega.
constructor.
apply Ord_le_Succ with (i := existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord_le_refl.
Qed.

Lemma n_lt_omega : forall (n : nat), n < omega.
Proof.
induction n as [| n IH]; simpl; split; unfold omega.

constructor.

intro H.
inversion_clear H as [| | f beta H'].
apply (ord_le_not_succ_zero Zero (H' 1)).

destruct IH as [H1 H2].
inversion_clear H1.
apply Ord_le_Succ with (i := existT (fun (n : nat) => pred_type n) 1 (inl (pred_type 0) tt)).
constructor.
destruct i as [[|m] t]; simpl in t, H.
elim t.
apply Ord_le_Succ with (i := existT (fun (n : nat) => pred_type n) (S m) t).
simpl.
Admitted.

Lemma lt : forall alpha beta, ((alpha <= beta /\ ~ beta <= alpha) <-> (exists i, alpha <= (pred beta i))).
Proof.
Admitted.

Close Scope ord_scope.
