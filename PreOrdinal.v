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


Set Implicit Arguments.


Delimit Scope ord'_scope with ord'.

Open Scope ord'_scope.

Inductive ord' : Set :=
  | Zero  : ord'
  | Succ  : ord' -> ord'
  | Limit : (nat -> ord') -> ord'.

Fixpoint pred_type (alpha : ord') : Set :=
  match alpha with
  | Zero       => False
  | Succ alpha => (unit + pred_type alpha) % type
  | Limit f    => { n : nat & pred_type (f n) }
  end.

Notation "!" := (False_rect _).

Fixpoint pred (alpha : ord') : pred_type alpha -> ord' :=
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

Reserved Notation "x <=' y" (no associativity, at level 75).

Inductive ord'_le : ord' -> ord' -> Prop :=
  | Ord'_le_Zero  : forall alpha,
                      Zero <=' alpha
  | Ord'_le_Succ  : forall alpha beta i,
                      alpha <=' pred beta i ->
                      Succ alpha <=' beta
  | Ord'_le_Limit : forall f beta,
                      (forall n, f n <=' beta) ->
                      Limit f <=' beta
where "alpha <=' beta" := (ord'_le alpha beta) : ord'_scope.



(* TODO: Why not  alpha < beta  <=>  alpha <= beta /\ ~ beta <= alpha  ? *)
(*Definition ord_lt (alpha beta : ord) := { t : pred_type beta & ord_le alpha (pred beta t) }.*)
(*Definition ord_lt alpha beta := alpha <= beta /\ ~ beta <= alpha.*)
Definition ord'_lt (alpha beta : ord') := exists i, alpha <=' (pred beta i).
Infix " <' " := ord'_lt (no associativity, at level 75) : ord'_scope.


(*
Lemma mm :
  forall alpha beta,
    alpha <' beta ->
    exists i, alpha = pred beta i.
Proof.
intros alpha beta H.
destruct H as [j H].
induction H as [alpha | alpha beta' k H IH |].

induction beta as [| beta IH' | f IH'].
elim j.
destruct IH' as [k H].
admit. (**)
exists (inr _ k).
assumption.
destruct (IH' 0) as [k H].
admit. (**)
exists (existT _ 0 k).
assumption.

induction beta as [| beta IH' | f IH'].
elim j.
destruct IH' as [i H1].
admit. (**)
destruct IH as [[i | i] H1].
simpl in H1.
admit. (* this proof is faulty *)
exists i.
assumption.
exists (inr _ i).
assumption.
destruct IH as [[n l] H1].
destruct (IH' n) as [h H2].
admit. (**)
exists l.
assumption.
exists (existT _ n h).
assumption.

Admitted.


(*
Inductive ord'_lt2 : ord' -> ord' -> Prop :=
  zz : forall alpha i, ord'_lt2 (pred alpha i) alpha.

Lemma ok : forall alpha beta, alpha <' beta <-> ord'_lt2 alpha beta.
split.
induction beta as [| beta _ | f _]; intro H; destruct H as [i H].
elim i.
*)
*)


(* Should we use this as our ordinal equality? Then <= is trivially
   antisymmetric, while it is not for structural equality.
   (I think this is fixed though, if we impose the increasing restriction
   of the limit functions) *)
Definition ord'_eq alpha beta := alpha <=' beta /\ beta <=' alpha.
Infix " ==' " := ord'_eq (no associativity, at level 75) : ord'_scope.

(* First predecessor of a successor is the original ordinal. *)
Lemma first_pred_after_succ_id :
  forall alpha, alpha = pred (Succ alpha) (inl (pred_type alpha) tt).
Proof.
trivial.
Qed.

(* No successor ordinal <= zero *)
Lemma ord'_le_not_succ_zero :
  forall alpha, ~ Succ alpha <=' Zero.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
Qed.

(* No double successor <= 1 *)
Lemma ord'_le_not_succ_succ_one :
  forall alpha, ~ Succ (Succ alpha) <=' Succ Zero.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
destruct u.
apply (@ord'_le_not_succ_zero alpha).
assumption.
assumption.
Qed.

(* If alpha <= zero, alpha <= any ordinal *)
Lemma ord'_le_zero_all :
  forall alpha beta,
    alpha <=' Zero ->
    alpha <=' beta.
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
Lemma ord'_le_pred_right :
  forall alpha beta (i : pred_type beta),
    alpha <=' pred beta i ->
    alpha <=' beta.
Proof.
induction alpha as [| alpha IH | f IH]; intros beta i H.
constructor.
apply Ord'_le_Succ with i.
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
Lemma ord'_le_pred_left :
  forall alpha beta (i : pred_type alpha),
    alpha <=' beta ->
    pred alpha i <=' beta.
Proof.
intros alpha beta i H.
induction H as [| alpha beta j H IH | f beta H IH].
destruct i.
destruct i as [[] | i']; apply ord'_le_pred_right with j.
apply H.
apply IH.
destruct i.
apply IH.
Qed.

(* If alpha <= beta, alpha <= the successor of beta *)
Lemma ord'_le_succ_right :
  forall alpha beta,
    alpha <=' beta ->
    alpha <=' Succ beta.
Proof.
induction alpha as [| alpha _ | f IH]; intros beta H.
constructor.
inversion_clear H.
apply Ord'_le_Succ with (inr unit i).
assumption.
constructor.
intro n.
apply IH.
inversion_clear H.
trivial.
Qed.

(* If the successor of alpha <= beta, alpha <= beta *)
Lemma ord'_le_succ_left :
  forall alpha beta,
    Succ alpha <=' beta ->
    alpha <=' beta.
Proof.
intros alpha beta H.
rewrite (first_pred_after_succ_id alpha).
apply ord'_le_pred_left.
assumption.
Qed.

(* If the successor of alpha <= the successor of beta, alpha <= beta *)
Lemma ord'_le_succ_elim :
  forall alpha beta,
    Succ alpha <=' Succ beta ->
    alpha <=' beta.
Proof.
inversion_clear 1.
destruct i as [[] |]; [| apply ord'_le_pred_right with p]; assumption.
Qed.

(* If the alpha <= beta, the successor of alpha <= the successor of beta *)
Lemma ord'_le_succ_intro :
  forall alpha beta,
    alpha <=' beta ->
    Succ alpha <=' Succ beta.
Proof.
intros.
apply Ord'_le_Succ with (inl (pred_type beta) tt).
assumption.
Qed.

(* No successor of alpha is <= alpha *)
Lemma ord'_le_not_succ :
  forall alpha, ~ Succ alpha <=' alpha.
Proof.
induction alpha as [| alpha IH | f IH]; intro H.
apply ord'_le_not_succ_zero with Zero.
assumption.
apply IH.
exact (ord'_le_succ_elim H).
inversion_clear H as [| a b i H' |].
inversion_clear H' as [| | a b H].
destruct i as [n i].
apply IH with n.
apply Ord'_le_Succ with i.
apply H.
Qed.

(* Suggested by Bruno Barras *)
(* If alpha <= a function value, alpha <= the limit of that function *)
Lemma ord'_le_limit_right :
  forall alpha f n,
    alpha <=' f n ->
    alpha <=' Limit f.
Proof.
induction alpha as [| alpha _ | f IH]; intros g n H.
constructor.
inversion_clear H.
apply Ord'_le_Succ with (existT (fun n => pred_type (g n)) n i).
assumption.
constructor.
intro m.
apply (IH m g n).
inversion_clear H.
trivial.
Qed.

(* If a limit <= alpha, any value value of the function <= alpha *)
Lemma ord'_le_limit_left :
  forall alpha f n,
    Limit f <=' alpha ->
    f n <=' alpha.
Proof.
intros alpha f n H.
inversion_clear H.
trivial.
Qed.

(* <= is reflexive *)
Lemma ord'_le_refl :
  forall alpha, alpha <=' alpha.
Proof.
induction alpha as [| alpha IH | f IH].
constructor.
apply Ord'_le_Succ with (inl (pred_type alpha) tt).
assumption.
constructor.
intro n.
apply ord'_le_limit_right with n.
apply IH.
Qed.

(* <= is transitive *)
Lemma ord'_le_trans :
  forall alpha beta gamma,
    alpha <=' beta ->
    beta <=' gamma ->
    alpha <=' gamma.
Proof.
intros alpha beta gamma H1.
revert gamma.
induction H1 as [| alpha beta i H IH | f beta H IH]; intros gamma H2.
constructor.
induction H2 as [| beta gamma j H' _ | f gamma H' IH'].
destruct i.
apply Ord'_le_Succ with j.
apply IH.
destruct i as [[] | i']; simpl in * |- *.
assumption.
apply ord'_le_pred_left.
assumption.
destruct i as [n i]; simpl in * |- *.
apply (IH' n i H IH).
constructor.
intro n.
exact (IH n gamma H2).
Qed.

(* We cannot prove this for = *)
(* <= is antisymmetric *)
Lemma ord'_le_antisymm :
  forall alpha beta,
    alpha <=' beta ->
    beta <=' alpha ->
    alpha ==' beta.
Proof.
intros.
unfold ord'_eq.
split; assumption.
Qed.

(* TODO: Can we prove <= is total? *)

(* == is reflexive *)
Lemma ord'_eq_refl :
  forall alpha, alpha ==' alpha.
Proof.
split; apply ord'_le_refl.
Qed.

(* == is symmetric *)
Lemma ord'_eq_symm :
  forall alpha beta,
    alpha ==' beta ->
    beta ==' alpha.
Proof.
split; apply H.
Qed.

(* == is transitive *)
Lemma ord'_eq_trans :
  forall alpha beta gamma,
    alpha ==' beta ->
    beta ==' gamma ->
    alpha ==' gamma.
Proof.
destruct 1.
destruct 1.
split; apply ord'_le_trans with beta; assumption.
Qed.

(* < is transitive *)
Lemma ord'_lt_trans :
  forall alpha beta gamma,
    alpha <' beta ->
    beta <' gamma ->
    alpha <' gamma.
Proof.
intros alpha beta gamma.
destruct 1 as [i].
destruct 1 as [j].
exists j.
apply ord'_le_trans with beta; [apply ord'_le_pred_right with i |]; assumption.
Qed.

(* TODO: find appropriate place for this lemma *)
Lemma ord'_lt_zero_zero :
  ~ Zero <' Zero.
Proof.
intro H.
destruct H as [i H].
elim i.
Qed.

(* TODO: move this lemma to a better place *)
Lemma ord'_le_not_pred_right_strong :
  forall alpha beta i,
    alpha <=' beta ->
    ~ beta <=' pred alpha i.
Proof.
induction alpha as [| alpha IH | f IH]; intros beta i H1 H2.
destruct i.
destruct i.
destruct u.
apply ord'_le_not_succ with alpha.
apply ord'_le_trans with beta; assumption.
exact (IH beta p (ord'_le_succ_left H1) H2).
destruct i.
inversion_clear H1.
exact (IH x beta p (H x) H2).
Qed.

(* TODO: move this lemma too *)
Lemma ord'_le_not_pred_right :
  forall alpha i, ~ alpha <=' pred alpha i.
Proof.
intros.
apply ord'_le_not_pred_right_strong.
apply ord'_le_refl.
Qed.

(* < is irreflexive *)
Lemma ord'_lt_irrefl :
  forall alpha, ~ alpha <' alpha.
Proof.
intros alpha H.
destruct H as [i H].
exact (ord'_le_not_pred_right i H).
Qed.

(* < is asymmetric *)
Lemma ord'_lt_asymm :
  forall alpha beta,
    alpha <' beta ->
    ~ beta <' alpha.
Proof.
intros alpha beta H1 H2.
destruct H1 as [i H1].
destruct H2 as [j H2].
apply (@ord'_le_not_pred_right_strong alpha beta j);
  [apply ord'_le_pred_right with i |]; assumption.
Qed.

(* If the successor of alpha < beta, alpha < beta *)
Lemma ord'_lt_succ_left :
  forall alpha beta,
    Succ alpha <' beta ->
    alpha <' beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
exists i.
apply ord'_le_succ_left.
assumption.
Qed.

(* If alpha < beta, alpha < the successor of beta *)
Lemma ord'_lt_succ_right :
  forall alpha beta,
    alpha <' beta ->
    alpha <' Succ beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
exists (inl (pred_type beta) tt).
apply ord'_le_pred_right with i.
assumption.
Qed.

(* If alpha < beta, alpha <= beta *)
Lemma ord'_lt_ord'_le :
  forall alpha beta, alpha <' beta -> alpha <=' beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
apply ord'_le_pred_right with i.
assumption.
Qed.

(* If alpha < beta, the successor of alpha <= beta *)
Lemma ord'_lt_ord'_le_succ :
  forall alpha beta,
    alpha <' beta ->
    Succ alpha <=' beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
apply Ord'_le_Succ with i.
assumption.
Qed.

(* TODO: move *)
Lemma ord'_lt_pred_right :
  forall alpha beta (i : pred_type beta),
    alpha <' pred beta i ->
    alpha <' beta.
Proof.
(* TODO *)
Admitted.

Lemma ord'_lt_not_ord'_le :
  forall alpha beta,
    alpha <' beta ->
    ~ beta <=' alpha.
Proof.
intros alpha beta H1 H2.
destruct H1 as [i H1].
apply (@ord'_le_not_pred_right_strong beta alpha i); assumption.
Qed.

(* TODO: this needs cleanup *)
Lemma sdfsdf :
  forall alpha beta i,
    alpha <=' pred (Succ beta) i ->
    alpha <=' beta.
Proof.
induction alpha; intros.
simpl in H.
destruct i.
destruct u.
assumption.
apply Ord'_le_Zero.
destruct beta.
destruct i.
destruct u.
destruct (ord'_le_not_succ_zero H).
destruct p.
apply Ord'_le_Succ with (inl (pred_type beta) tt).
simpl.
simpl in H.
destruct i.
destruct u.
apply ord'_le_succ_elim.
assumption.
destruct p.
apply ord'_le_succ_left.
destruct u.
assumption.
apply ord'_le_succ_left.
apply ord'_le_pred_right with p.
assumption.
simpl in H.
destruct i.
destruct u.
assumption.
destruct p.
apply ord'_le_limit_right with x.
apply ord'_le_pred_right with p.
assumption.
apply Ord'_le_Limit.
intro.
inversion_clear H0.
apply H with i.
apply H1.
Qed.

(* If alpha < beta and beta <= gamma, alpha < gamma *)
(* TODO: variations and move to appropriate place *)
Lemma ord'_lt_trans_ord'_le_right :
  forall alpha beta gamma,
    alpha <' beta ->
    beta <=' gamma ->
    alpha <' gamma.
Proof.
intros.
destruct H.
destruct gamma.
assert (H1 := ord'_le_zero_all (pred beta x) H0).
destruct (ord'_le_not_pred_right x H1).
destruct H0.
destruct x.
exists i.
apply ord'_le_trans with alpha0.
simpl in H.
apply sdfsdf with x.
assumption.
assumption.
(* TODO: we need this *)
Admitted.

(* Image of naturals in pre-ordinals *)
Fixpoint nat_as_ord' (n : nat) : ord' :=
  match n with
  | O   => Zero
  | S n => Succ (nat_as_ord' n)
  end.

Coercion nat_as_ord' : nat >-> ord'.

Lemma lt_nat_ord' : forall n m, (n < m)%nat -> n <' m.
Proof.
(* TODO: see old proof below *)
Admitted.

Lemma lt_ord'_nat : forall (n m : nat), n <' m -> (n < m)%nat.
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

(*
Axiom ord'_le_pi : forall alpha beta (H H' : alpha <=' beta), H = H'.
Axiom ord'_lt_pi : forall alpha beta (H H' : alpha <' beta), H = H'.
*)


Close Scope ord'_scope.
