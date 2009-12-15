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

Delimit Scope ordinal_scope with ord.

Open Scope ordinal_scope.

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

Definition ord_eq (alpha beta : ord) := ord_le alpha beta /\ ord_le beta alpha.

Definition ord_lt (alpha beta : ord) := { t : pred_type beta & ord_le alpha (pred beta t) }.

Notation "alpha <= beta" := (ord_le alpha beta) : ordinal_scope.
Notation "alpha < beta" := (ord_lt alpha beta) : ordinal_scope.

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
elim i.
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
(* TODO: move beta to front *)
Lemma ord_le_zero_all :
  forall alpha,
    alpha <= Zero ->
    forall beta,
      alpha <= beta.
Proof.
induction alpha as [| alpha IHs | f IHl]; intros H beta.
constructor.
inversion_clear H.
elim i.
inversion_clear H.
constructor.
intro n.
apply IHl.
apply H0.
Qed.

(* If alpha <= a predecessor of beta, alpha <= beta *)
Lemma ord_le_pred_right :
  forall alpha beta (i : pred_type beta),
    alpha <= pred beta i ->
    alpha <= beta.
Proof.
induction alpha as [| alpha IHs | f IHl]; intros beta i H.
constructor.
apply Ord_le_Succ with i.
inversion_clear H.
apply IHs with i0.
assumption.
constructor.
intro n.
inversion_clear H.
apply IHl with i.
auto.
Qed.

(* If alpha <= beta, all predecessors of alpha <= beta *)
(* TODO: i to front *)
Lemma ord_le_pred_left :
  forall alpha beta,
    alpha <= beta ->
    forall (i : pred_type alpha), pred alpha i <= beta.
Proof.
induction 1; simpl; intros.
destruct i.
destruct i0 as [[]|j'].
apply ord_le_pred_right with (1:=H).
apply ord_le_pred_right with (1:=IHord_le j').
destruct i.
apply H0.
Qed.

(* If alpha <= beta, alpha <= the successor of beta *)
Lemma ord_le_succ_right :
  forall alpha beta,
    alpha <= beta ->
    alpha <= Succ beta.
Proof.
induction alpha as [| alpha IHs | f IHl]; intros beta H.
constructor.
inversion_clear H.
apply Ord_le_Succ with (i := inr unit i).
assumption.
constructor.
intro n.
apply IHl.
inversion_clear H.
apply H0.
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

(* Suggested by Bruno Barras *)
(* If alpha <= a function value, alpha <= the limit of that function *)
Lemma ord_le_limit_right :
  forall alpha f n,
    alpha <= f n ->
    alpha <= Limit f.
Proof.
induction alpha as [| alpha IHs | f IHl]; intros g n H.
constructor.
inversion_clear H.
apply Ord_le_Succ with (i := existT (fun n => pred_type (g n)) n i).
assumption.
constructor.
intro m.
apply (IHl m g n).
inversion_clear H.
apply H0.
Qed.

(* If a limit <= alpha, any value value of the function <= alpha *)
Lemma ord_le_limit_left :
  forall alpha f n,
    Limit f <= alpha ->
    f n <= alpha.
Proof.
(* TODO *)
Admitted.

(* <= is reflexive *)
Lemma ord_le_refl :
  forall alpha, alpha <= alpha.
Proof.
induction alpha as [| alpha IHs | f IHl].
constructor.
apply Ord_le_Succ with (i := inl (pred_type alpha) tt).
assumption.
constructor.
intro n.
apply ord_le_limit_right with n.
apply IHl.
Qed.

(* <= is transitive *)
(* TODO: move gamma to front *)
Lemma ord_le_trans :
  forall alpha beta,
    alpha <= beta ->
    forall gamma,
      beta <= gamma ->
      alpha <= gamma.
Proof.
intros a b.
induction 1 as [ beta | alpha beta i H IHs | f beta H IHl ]; intros gamma Hbc.
constructor.
induction Hbc as [ gamma | beta gamma j H0 _ | f gamma H0 IHbc ].
destruct i.
apply Ord_le_Succ with j.
apply IHs.
destruct i as [[]|i']; simpl in *|-*.
exact H0.
fold pred_type in i'.
apply ord_le_pred_left.
exact H0.
destruct i as [n i]; simpl in *|-*.
fold pred_type in i.
apply IHbc with (1:=H) (2:=IHs).
constructor.
intro n.
exact (IHl n gamma Hbc).
Qed.

(*
Lemma ord_le_trans : forall (alpha beta gamma : ord), ord_le alpha beta ->
                       ord_le beta gamma -> ord_le alpha gamma.
Proof.
induction alpha as [| alpha IHs | f IHl].
constructor.
intros beta gamma H1 H2.
destruct H2.
inversion_clear H1.
inversion i.
apply Ord_le_Succ with (i := i).
apply IHs with (beta := alpha0).
apply ord_le_succ.
assumption.
assumption.
apply Ord_le_Succ.
(* we've gone wrong it seems... *)
*)

(*
Lemma ord_le_succ :
  forall (alpha beta : ord),
    ord_le (Succ alpha) (Succ beta) ->
    ord_le alpha beta.
Proof.
induction alpha; destruct beta.
constructor.
constructor.
constructor.
intro H.
inversion_clear H.


inversion_clear H0.
inversion_clear i0.

contradiction with ord_le_not_succ_zero.



intros alpha beta H.

destruct beta.


inversion_clear H.


Admitted.
*)
