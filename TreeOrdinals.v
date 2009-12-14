(*
  Formalisation of tree ordinals based on the notes:

    Peter Hancock, "Ordinal theoretic proof theory"

  See also the formalisation in Isabelle by Michael Compton:
  http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html
*)

Inductive ord : Set :=
  | Zero  : ord
  | Succ  : ord -> ord
  | Limit : (nat -> ord) -> ord.

Definition fam (A : Type) : Type := { I : Set & I -> A }.
Definition pow (A : Type) : Type := A -> Set.

Fixpoint pred_type (alpha : ord) : Set :=
  match alpha with
  | Zero       => False
  | Succ alpha => (unit + pred_type alpha) % type
  | Limit f    => { n : nat & pred_type (f n) }
  end.

Definition zero z := pred_type z -> False.

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

Definition pd (alpha : ord) : fam ord := existT _ (pred_type alpha) (pred alpha).

Inductive ord_le : ord -> ord -> Prop :=
  | Ord_le_Zero : forall alpha, ord_le Zero alpha
  | Ord_le_Succ : forall (alpha beta : ord) (i : pred_type beta),
                  ord_le alpha (pred beta i) -> ord_le (Succ alpha) beta
  | Ord_le_Limit : forall (f : nat -> ord) (beta : ord),
                   (forall n, ord_le (f n) beta) -> ord_le (Limit f) beta.

(* Volgens mij is het kantine lemma niet waar, er bestaat _een_ i zodat
   ord_le alpha (pred beta i), maar dit is niet zo voor alle i *)
Lemma kantine :
  forall (alpha beta : ord) (i : pred_type beta),
  ord_le (Succ alpha) beta -> ord_le alpha (pred beta i).
Proof.
intros alpha beta t H.
inversion_clear H.
(* ? *)
Admitted.

(* No successor ordinal is le than zero *)
Lemma ord_le_not_succ_zero :
  forall (alpha : ord),
    ord_le (Succ alpha) Zero -> False.
Proof.
intros alpha H.
inversion_clear H.
elim i.
Qed.

(* No double successor is le than 1 *)
Lemma ord_le_not_succ_succ_one : forall (alpha : ord),
  ord_le (Succ (Succ alpha)) (Succ Zero) -> False.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
destruct u.
apply (ord_le_not_succ_zero alpha).
assumption.
assumption.
Qed.

(* If alpha is le than a predecessor of beta, alpha is le than beta *)
Lemma ord_le_pred_right :
  forall (alpha beta : ord) (i : pred_type beta),
    ord_le alpha (pred beta i) ->
    ord_le alpha beta.
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

(* If alpha is le than beta, all predecessors of alpha are le than beta *)
Lemma ord_le_pred_left :
  forall alpha beta,
    ord_le alpha beta ->
    forall (i : pred_type alpha), ord_le (pred alpha i) beta.
Proof.
induction 1; simpl; intros.
destruct i.
destruct i0 as [[]|j'].
apply ord_le_pred_right with (1:=H).
apply ord_le_pred_right with (1:=IHord_le j').
destruct i.
apply H0.
Qed.

(*
Lemma ord_le_succ_mm :
  forall (alpha beta : ord),
    ord_le (Succ alpha) beta ->
    ord_le alpha beta.
*)

(*
Lemma mmm :
  forall (alpha beta : ord),
    (ord_le alpha beta -> False) ->
    ord_le (Succ alpha) (Succ beta) ->
    False.
Proof.
intros alpha beta H1 H2.
inversion_clear H2.
destruct i.
destruct u.
exact (H1 H).
apply H1.
Admitted.
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

(* If alpha is le than beta, alpha is le than the successor of beta *)
Lemma ord_le_succ_right :
  forall (alpha beta : ord),
    ord_le alpha beta ->
    ord_le alpha (Succ beta).
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

(* Suggested by Bruno Barras
   If alpha is le than a function value, alpha is le than the limit of that function *)
Lemma ord_le_limit_right :
  forall (alpha : ord) (f : nat -> ord) (n : nat),
    ord_le alpha (f n) ->
    ord_le alpha (Limit f).
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

(*
Lemma sfsdfds : forall (alpha beta : ord) (i : pred_type beta),
  ord_le alpha (pred beta i) ->
  ord_le alpha beta.
Proof.
induction alpha as [| alpha IHs | f IHl]; intros beta i H.
constructor.
apply Ord_le_Succ with (i := i).
(* ... *)
apply (IHs (pred beta i) (inr (pred_type beta) i)).
*)

(* ord_le is reflexive *)
Lemma ord_le_refl :
  forall (alpha : ord),
    ord_le alpha alpha.
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

(* If alpha is le than zero, alpha is le than any ordinal *)
Lemma zz :
  forall alpha,
    ord_le alpha Zero ->
    forall beta,
      ord_le alpha beta.
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

(* ord_le is transitive *)
Lemma ord_le_trans :
  forall (alpha beta : ord),
    ord_le alpha beta ->
    forall gamma,
      ord_le beta gamma ->
      ord_le alpha gamma.
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

Definition ord_eq (alpha beta : ord) := ord_le alpha beta /\ ord_le beta alpha.

Definition ord_lt (alpha beta : ord) := { t : pred_type beta & ord_le alpha (pred beta t) }.
