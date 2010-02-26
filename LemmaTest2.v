(* Try a different pred_type for Limit (suggestion 1 in LemmaTest1.v comments *)


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
  | Limit f    => nat (* different *)
  end.

Notation "!" := (False_rect _).

Fixpoint pred (alpha : ord') : pred_type alpha -> ord' :=
  match alpha with
  | Zero       => !
  | Succ alpha => fun i => match i with
                           | inl tt => alpha
                           | inr t  => pred alpha t
                           end
  | Limit f    => fun n => f n (* different *)
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

Definition ord'_lt (alpha beta : ord') := exists i, alpha <=' (pred beta i).
Infix " <' " := ord'_lt (no associativity, at level 75) : ord'_scope.

(* No successor ordinal <= zero *)
Lemma ord'_le_not_succ_zero :
  forall alpha, ~ Succ alpha <=' Zero.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
Qed.

Lemma ord'_lt_zero_zero :
  ~ Zero <' Zero.
Proof.
intro H.
destruct H as [i H].
elim i.
Qed.

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

Lemma ord'_le_limit_right :
  forall alpha f n,
    alpha <=' f n ->
    alpha <=' Limit f.
Proof.
induction alpha as [| alpha _ | f IH]; intros g n H.
constructor.
inversion_clear H.
apply Ord'_le_Succ with n.
apply ord'_le_pred_right with i.
assumption.
constructor.
intro m.
apply (IH m g n).
inversion_clear H.
trivial.
Qed.

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

Lemma ord'_le_pred_left :
  forall alpha beta (i : pred_type alpha),
    alpha <=' beta ->
    pred alpha i <=' beta.
Proof.
intros alpha beta i H.
induction H as [| alpha beta j H IH | f beta H _].
destruct i.
destruct i as [[] | i']; apply ord'_le_pred_right with j.
apply H.
apply IH.
apply H.
Qed.

Lemma ord'_le_trans :
  forall alpha beta gamma,
    alpha <=' beta ->
    beta <=' gamma ->
    alpha <=' gamma.
Proof.
Admitted.
(*
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
*)

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

Lemma ord'_lt_trans_ord'_le_right :
  forall alpha beta gamma,
    alpha <' beta ->
    beta <=' gamma ->
    alpha <' gamma.
Proof.
intros.
destruct H.
destruct gamma.
(*
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
*)
(* TODO: we need this *)
Admitted.

Fixpoint good alpha : Prop :=
  match alpha with
  | Zero      => True
  | Succ beta => good beta
  | Limit f   => forall n, good (f n) /\ forall m, (n < m)%nat -> (f n) <' (f m)
  end.


Ltac expl_case x :=
  generalize (refl_equal x); pattern x at -1; case x; intros until 1.

(* This is part of ord_le_zero_good and should be separated from it (Ordinals.v) *)
Lemma ord'_le_zero_good :
  forall alpha,
    good alpha ->
    alpha <=' Zero ->
    alpha = Zero.
Proof.
induction alpha as [| | f IH]; intros G H.
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

Lemma uu :
  forall alpha,
  good alpha ->
  (exists i : pred_type alpha, True) \/ Zero = alpha.
Proof.
induction alpha as [alpha | alpha IH | f IH]; simpl; intro g.
right; reflexivity.
left.
exists (inl _ tt); constructor.
left.
elim (IH 1 (proj1 (g 1))); intro H.
destruct H as [i H'].
exists 1.
constructor.
destruct (g 0) as [H1 H2].
assert (H3 : f 0 <' f 1).
apply H2; auto.
unfold ord'_lt in H3.
elim H3; intros i _.
rewrite <- H in i.
elim i.
Qed.

Lemma vv :
  forall alpha i,
    good alpha -> good (pred alpha i).
Proof.
induction alpha as [| alpha IH | f IH]; intros i g; destruct i.
destruct u.
assumption.
apply IH.
assumption.
apply g.
apply g.
Qed.

(*
Lemma ww :
  forall f alpha,
    (forall n, exists i, f n <=' pred alpha i) ->
    exists i, Limit f <=' pred alpha i.
Proof.
intros f alpha H.
destruct alpha.
destruct (H 0) as [[] _].
exists (inl _ tt).
constructor.
intro.
destruct (H n) as [[[] | i] H1].
assumption.
apply ord'_le_pred_right with i.
assumption.
*)

Lemma xx :
  forall alpha beta,
  alpha <=' beta ->
  good alpha ->
  good beta ->
  (exists i, alpha <=' pred beta i) \/ alpha = beta.
Proof.
induction 1 as [alpha | alpha beta i H IH | f beta H IH]; intros ga gb.

(* 1. Case Zero <=' pred beta i \/ Zero = beta *)
elim (uu alpha gb); intro H.
destruct H as [i _].
left; exists i; constructor.
right; exact H.

(* 2. Case Succ alpha <=' pred beta i \/ Succ alpha = beta *)
destruct IH as [IH | e].
assumption.
apply vv.
assumption.

(* 2.1 Left side of IH *)
left.
destruct IH as [j IH].
exists i.
apply Ord'_le_Succ with j.
assumption.

(* 2.2 Right side of IH *)
induction beta as [| beta IH | f _].

(* 2.2.1 Case beta => Zero *)
elim i.

(* 2.2.2 Case beta => Succ beta *)
destruct i as [[] | i].
right.
rewrite e.
reflexivity.
left.
destruct (IH i H e gb) as [[j H1] | H1]; clear IH.
exists (inr unit j).
assumption.
exists (inl _ tt).
rewrite H1.
apply ord'_le_refl.

(* 2.2.3 Case beta => Limit f *)
left.
exists (S i).
destruct (proj2 (gb i) (S i)) as [j H1].
auto.
simpl in H.
apply Ord'_le_Succ with j.
apply ord'_le_trans with (f i).
assumption.
assumption.

(*left.*)
destruct beta.

destruct (proj2 (ga 0) 1) as [i _].
auto.
rewrite (ord'_le_zero_good (proj1 (ga 1)) (H 1)) in i.
elim i.

left.
exists (inl _ tt).
constructor.
intro n.
destruct (proj2 (ga n) (S n)) as [i H1].
auto.
simpl.
assert (H2 : f n <' Succ beta).
apply ord'_lt_trans_ord'_le_right with (f (S n)).
exists i.
assumption.
apply H.
unfold ord'_lt in H2.
destruct H2 as [[[] | j] H2].
assumption.
apply ord'_le_pred_right with j.
assumption.

(* and we are stuck again *)
Admitted.
