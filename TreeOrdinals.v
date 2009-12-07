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

Lemma ord_le_not_succ_zero : forall (alpha : ord),
  ord_le (Succ alpha) Zero -> False.
Proof.
intros alpha H.
inversion_clear H.
inversion_clear i.
Qed.

Lemma aaa : forall (alpha beta : ord) (i : pred_type beta),
  ord_le alpha (pred beta i) -> ord_le alpha beta.
Proof.
Admitted.

Lemma mmm : forall (alpha beta : ord),
  (ord_le alpha beta -> False) -> ord_le (Succ alpha) (Succ beta) -> False.
Proof.
intros alpha beta H1 H2.
inversion_clear H2.
destruct i.
destruct u.
exact (H1 H).
apply H1.


Admitted.

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

(*
Lemma ord_le_succ : forall (alpha beta : ord),
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

Lemma ord_le_Succ_r : forall (alpha beta : ord),
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

(* Suggested by Bruno Barras *)
Lemma ord_le_Limit_r : forall (alpha : ord) (f : nat -> ord) (n : nat),
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


Lemma ord_le_refl : forall (alpha : ord), ord_le alpha alpha.
Proof.
induction alpha as [| alpha IHs | f IHl].
constructor.
apply Ord_le_Succ with (i := inl (pred_type alpha) tt).
assumption.
constructor.
intro n.
apply ord_le_Limit_r with (n := n).
apply IHl.
Qed.

Lemma ord_le_trans : forall (alpha beta gamma : ord), ord_le alpha beta ->
                       ord_le beta gamma -> ord_le alpha gamma.
Proof.
intros alpha beta gamma H1 H2.
destruct H2.
inversion_clear H1.
constructor.
inversion_clear i.
admit.
Admitted.

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
Definition Ord_eq (o p : Ord) := (Ord_le o p, Ord_le p o).

Definition Ord_lt (o p : Ord) := { t : Pd p & Ord_le o (Pd_pd p t) }.
*)
