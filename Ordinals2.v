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

(*
Fixpoint ord_le_bool (alpha : ord) : ord -> bool :=
  fun beta => 
  match alpha with 
  | Zero => true
  | Succ alpha => 
  match beta with
  | Zero => false
  | Succ beta => ord_le_bool alpha beta
  | Lim f => ???
end.
*)

Inductive ord_le : ord -> ord -> Type :=
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
(*Definition ord_lt alpha beta := alpha <= beta /\ ~ beta <= alpha.*)
Definition ord_lt (alpha beta : ord) := sigT (fun i => alpha <= pred beta i).
Infix " < " := ord_lt : ord_scope.

(* Should we use this as our ordinal equality? Then <= is trivially
   antisymmetric, while it is not for structural equality.
   (I think this is fixed though, if we impose the increasing restriction
   of the limit functions) *)
Definition ord_eq alpha beta := alpha <= beta * beta <= alpha.
Infix " == " := ord_eq (no associativity, at level 75) : ord_scope.

(* First predecessor of a successor is the original ordinal. *)
Lemma first_pred_after_succ_id :
  forall alpha, alpha = pred (Succ alpha) (inl (pred_type alpha) tt).
Proof.
trivial.
Qed.


Inductive empty : Type :=.

(* No successor ordinal <= zero *)
Lemma ord_le_not_succ_zero :
  forall alpha, Succ alpha <= Zero -> empty.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
Qed.

(*
(* No double successor <= 1 *)
Lemma ord_le_not_succ_succ_one :
  forall alpha, Succ (Succ alpha) <= Succ Zero -> empty.
Proof.
intros alpha H.
inversion_clear H.
destruct i.
destruct u.
apply (ord_le_not_succ_zero alpha).
assumption.
assumption.
Qed.
*)

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
(*
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
*)
Definition disc_O_S : forall (alpha : ord), Zero <> Succ alpha :=
  fun alpha H =>
  let P := (fun beta : ord => match beta with Zero => (False -> False) | Succ beta => False | Limit f => False end) in 
  match H in (_ = q) return P q with refl_equal => (fun a => a) end.


Definition disc_O_L : forall (f : nat -> ord), Zero <> Limit f :=
  fun f H =>
  let P := (fun beta : ord => match beta with Zero => (False -> False) | Succ beta => False | Limit f => False end) in 
  match H in (_ = q) return P q with refl_equal => (fun a => a) end.

Definition disc_L_S : forall (f : nat -> ord) (alpha : ord), Limit f <> Succ alpha :=
  fun alpha f H =>
  let P := (fun beta : ord => match beta with Zero => False | Succ beta => False | Limit f => False -> False end) in 
  match H in (_ = q) return P q with refl_equal => (fun a => a) end.

Definition S_eq_inv : forall alpha alpha', Succ alpha = Succ alpha' -> alpha = alpha'.
Admitted.

Definition rewrite (X : Type) (P : X -> Type) (x y : X) (e : x = y) (p : P x) : P y :=
  match e in _ = y return P y with 
  | refl_equal => p
  end.

Definition ord_le_Succ_inv :
  forall (alpha beta : ord), 
  Succ alpha <= beta -> 
  sigT (fun i : pred_type beta => alpha <= pred beta i) :=
  fun alpha beta H =>
  match H in (Salpha <= beta) 
          return Salpha = Succ alpha 
                 -> sigT (fun i : pred_type beta, alpha <= pred beta i) 
          with
  | Ord_le_Zero beta => 
      fun e : Zero = Succ alpha => False_rect _ (disc_O_S alpha e)
  | Ord_le_Succ alpha' beta i H0 => 
      fun e : Succ alpha' = Succ alpha => 
      existT (fun i : pred_type beta => alpha <= pred beta i) 
             i (rewrite _ (fun a => a <= pred beta i) _ _ (S_eq_inv _ _ e) H0)
  | Ord_le_Limit f beta H0 => fun e => False_rect _ (disc_L_S f alpha e)
end (refl_equal (Succ alpha)).

Definition ord_le_limit_inv :
  forall (f : nat -> ord) (beta : ord), 
  Limit f <= beta -> 
  forall n, f n <= beta :=
  fun f beta H => 
  match H in Limit_f <= beta return Limit_f = Limit f -> forall n, f n <= beta with
  | Ord_le_Zero beta => fun e : Zero = Limit f => False_rect _ (disc_O_L f e)
  | Ord_le_Succ alpha beta i H0 => 
      fun e : Succ alpha = Limit f => False_rect _ (disc_L_S f alpha (sym_eq e))
  | Ord_le_Limit f' beta H0 => 
      fun e : Limit f' = Limit f => 
      rewrite _ (fun g : nat -> ord => forall n, g n <= beta) _ _ 
      (f_equal (fun o : ord => match o with Zero => f' | Succ _ => f' | Limit f'' => f'' end) e) 
      H0
  end (refl_equal (Limit f)).

Fixpoint ord_le_pred_right' (alpha : ord) : 
  forall (beta : ord) (i : pred_type beta), alpha <= pred beta i -> alpha <= beta :=
  fun beta i =>
  match alpha as a return a <= pred beta i -> a <= beta with 
  | Zero        => fun _ => Ord_le_Zero beta
  | Succ alpha' => 
    fun H : Succ alpha' <= pred beta i => 
    Ord_le_Succ alpha' beta i 
      (ord_le_pred_right' alpha' (pred beta i) 
        (projT1 (ord_le_Succ_inv _ _ H)) (projT2 (ord_le_Succ_inv _ _ H)))
  | Limit f => 
      fun H : Limit f <= pred beta i => 
      Ord_le_Limit f beta (fun n => (ord_le_pred_right' (f n) beta i (ord_le_limit_inv f (pred beta i) H n)))
end.

Definition ord_le_pred_right := ord_le_pred_right'.

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
(*
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
Defined.
*)

Fixpoint ord_le_succ_right' (alpha beta : ord) (H : alpha <= beta) : alpha <= Succ beta :=
  match H in alpha <= beta return alpha <= Succ beta with 
  | Ord_le_Zero beta => Ord_le_Zero (Succ beta)
  | Ord_le_Succ alpha beta i H0 => Ord_le_Succ alpha (Succ beta) (inr unit i) H0
  | Ord_le_Limit f beta H0 => 
      Ord_le_Limit f (Succ beta) (fun n => (ord_le_succ_right' (f n) beta (H0 n)))
end.

Definition ord_le_succ_right := ord_le_succ_right'.

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

(* No successor of alpha is <= alpha *)
(*
Lemma ord_le_not_succ :
  forall alpha, ~ Succ alpha <= alpha.
Proof.
induction alpha as [| alpha IH | f IH]; intro H.
apply ord_le_not_succ_zero with Zero.
assumption.
apply IH.
apply (ord_le_succ (Succ alpha) alpha H).
inversion_clear H as [| a b i H' |].
inversion_clear H' as [| | a b H].
destruct i as [n i].
apply IH with n.
apply Ord_le_Succ with i.
apply H.
Qed.
*)

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
Qed.

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
(*
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
*)

(* TODO: Can we prove <= is total? *)

(* == is reflexive *)
(*
Lemma ord_eq_refl :
  forall alpha, alpha == alpha.
Proof.
split; apply ord_le_refl.
Qed.
*)

(* == is symmetric *)
(*
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

(* TODO: move this lemma to a better place *)
Lemma ord_le_not_pred_right_strong :
  forall alpha beta i,
    alpha <= beta ->
    ~ beta <= pred alpha i.
Proof.
induction alpha as [| alpha IH | f IH]; intros beta i H1 H2.
destruct i.
destruct i.
destruct u.
apply ord_le_not_succ with alpha.
apply ord_le_trans with beta; assumption.
exact (IH beta p (ord_le_succ_left alpha beta H1) H2).
destruct i.
inversion_clear H1.
exact (IH x beta p (H x) H2).
Qed.

(* TODO: move this lemma too *)
Lemma ord_le_not_pred_right :
  forall alpha i, ~ alpha <= pred alpha i.
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
exact (ord_le_not_pred_right alpha i H).
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
apply (ord_le_not_pred_right_strong alpha beta j);
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
Defined. (**)
*)

(* If alpha < beta, alpha <= beta *)
Lemma ord_lt_ord_le :
  forall alpha beta, alpha < beta -> alpha <= beta.
Proof.
intros alpha beta.
destruct 1 as [i H].
apply ord_le_pred_right with i.
assumption.
Defined.

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
Defined.

(* TODO: move *)
Lemma ord_lt_pred_right :
  forall alpha beta (i : pred_type beta),
    alpha < pred beta i ->
    alpha < beta.
Proof.
(* TODO *)
Admitted.

(*
Lemma ord_lt_not_le :
  forall alpha beta,
    alpha < beta ->
    ~ beta <= alpha.
Proof.
intros alpha beta H1 H2.
destruct H1 as [i H1].
apply (ord_le_not_pred_right_strong beta alpha i); assumption.
Qed.

(* TODO: this needs cleanup *)
Lemma sdfsdf :
  forall alpha beta i,
    alpha <= pred (Succ beta) i ->
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
destruct (ord_le_not_succ_zero alpha H).
destruct p.
apply Ord_le_Succ with (inl (pred_type beta) tt).
simpl.
simpl in H.
destruct i.
destruct u.
apply ord_le_succ.
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
Lemma ord_lt_trans_le_right :
  forall alpha beta gamma,
    alpha < beta ->
    beta <= gamma ->
    alpha < gamma.
Proof.
intros.
destruct H.
destruct gamma.
assert (H1 := ord_le_zero_all beta (pred beta x) H0).
destruct (ord_le_not_pred_right beta x H1).
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

(*
   Below we try to separate the good from the bad
*)
*)
(* Good ordinals are those where the limit functions are increasing *)
Fixpoint good alpha : Type :=
  match alpha with
  | Zero      => True
  | Succ beta => good beta
  | Limit f   => forall n, good (f n) * forall m, (n < m)%nat -> (f n) < (f m)
  end.

(* TODO: find appropriate place for this lemma *)
Lemma ord_lt_zero_zero :
  Zero < Zero -> empty.
Proof.
intro H.
destruct H as [i H].
elim i.
Qed.

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
elimtype empty.
apply ord_lt_zero_zero.
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

(* If the successor of alpha is good, alpha is good *)
Lemma good_succ_elim :
  forall alpha,
    good (Succ alpha) ->
    good alpha.
Proof.
intros.
assumption.
Qed.

(* If alpha is good, the successor of alpha is good *)
Lemma good_succ_intro :
  forall alpha,
    good alpha ->
    good (Succ alpha).
Proof.
intros.
assumption.
Qed.

(* TODO: redo this for new < definition *)
(*
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
TODO: Weird, why does this not work when Setoid is not required?

  Require Import Setoid.
  Definition omega := Limit id.

But the following does work:

  Definition id' (n : nat) : ord := id n.
  Definition omega := Limit id'.

We have our coercion nat_as_ord, but for some reason it is not used when
the Setoid module is required.
*)
Definition omega := Limit (fun o => o).

Lemma n_le_omega : forall (n : nat), n <= omega.
Proof.
induction n as [| n IH]; simpl; unfold omega.
constructor.
apply Ord_le_Succ with (i := existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord_le_refl.
Qed.

Lemma n_lt_omega : forall (n : nat), n < omega.
Proof.
intro n.
exists (existT (fun (n:nat) => pred_type n) (S n) (inl (pred_type n) tt)).
apply ord_le_refl.
Qed.

(*
Lemma lt_right : forall alpha beta, alpha <= beta /\ ~ beta <= alpha -> exists i, alpha <= (pred beta i).
Proof.
intros alpha beta H.
destruct H as [H1 H2].

induction beta as [| beta _ | f IH].
(* beta might not be the right choice here... *)

contradict H2.
constructor.

exists (inl (pred_type beta) tt).
simpl.
Admitted.

Lemma lt_left : forall alpha beta, (exists i, alpha <= (pred beta i)) -> alpha <= beta /\ ~ beta <= alpha.
split.

destruct alpha.

constructor.

elim H.
intros.
apply Ord_le_Succ with x.
apply (ord_le_succ_left alpha (pred beta x) H0).

elim H.
intros.
constructor.
inversion_clear H0.
intro.
apply (ord_le_pred_right (o n) beta x).
apply H1.

intro H1.
elim H.
intros.
destruct alpha.

destruct beta.
destruct x.
inversion_clear H1.

Admitted.

Definition is_limit o : Prop := exists f, Limit f = o.
*)

Close Scope ord_scope.
