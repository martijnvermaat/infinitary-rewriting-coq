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
                     ord_le Zero alpha
  | Ord_le_Succ  : forall (alpha beta : ord) (i : pred_type beta),
                     ord_le alpha (pred beta i) ->
                     ord_le (Succ alpha) beta
  | Ord_le_Limit : forall (f : nat -> ord) (beta : ord),
                     (forall n, ord_le (f n) beta) ->
                     ord_le (Limit f) beta.

(* Should we use this as our ordinal equality? Then <= is trivially
   antisymmetric, while it is not for structural equality.
   (I think this is fixed though, if we impose the increasing restriction
   of the limit functions) *)
Definition ord_eq (alpha beta : ord) := ord_le alpha beta /\ ord_le beta alpha.

(* Why not  alpha < beta  <=>  alpha <= beta /\ ~ beta <= alpha  ? *)
(*Definition ord_lt (alpha beta : ord) := { t : pred_type beta & ord_le alpha (pred beta t) }.*)
Definition ord_lt (alpha beta : ord) := exists i, ord_le alpha (pred beta i).

Infix "<=" := ord_le : ord_scope.
Infix "==" := ord_eq (no associativity, at level 75) : ord_scope.
Infix "<" := ord_lt : ord_scope.

(* First predecessor of a successor is the original ordinal. *)
Lemma first_pred_after_succ_id :
  forall alpha, alpha = pred (Succ alpha) (inl (pred_type alpha) tt).
Proof.
trivial.
Qed.

(* No successor ordinal <= zero *)
Lemma ord_le_not_succ_zero :
  forall alpha, Succ alpha <= Zero -> False.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
Qed.

(* No double successor <= 1 *)
Lemma ord_le_not_succ_succ_one :
  forall alpha, Succ (Succ alpha) <= Succ Zero -> False.
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

Close Scope ord_scope.
