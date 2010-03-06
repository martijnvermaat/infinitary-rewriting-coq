(* Inductive defintion for rewriting sequences *)


Require Import Prelims.
Require Export List.
Require Export FiniteTerm.
Require Export Term.
Require Import Substitution.
Require Import Context.
Require Export PreOrdinal.
Require Export TermEquality.


Set Implicit Arguments.


Section Rule.

Variable F : signature.
Variable X : variables.

Notation fterm := (finite_term F X).

(* Rewriting rules of finite terms *)
Record rule : Type := Rule {
  lhs     : fterm;
  rhs     : fterm;
  rule_wf : is_var lhs = false /\ incl (vars rhs) (vars lhs)
}.

(* Left hand side is linear *)
Definition left_linear (r : rule) : Prop :=
  linear (lhs r).

(* A Term Rewriting System as a finite list of of rewriting rules *)
Definition trs := list rule.

(* All rules are left-linear *)
Fixpoint trs_left_linear (s : trs) : Prop :=
  match s with
  | nil   => True
  | r::rs => left_linear r /\ trs_left_linear rs
  end.

End Rule.


Implicit Arguments rule [F X].


Section TRS.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation context := (context F X).
Notation substitution := (substitution F X).
Notation trs := (trs F X).

Variable system : trs.

(* Only needed in Coq 8.3 *)
Generalizable All Variables.

Reserved Notation "s [>] t" (no associativity, at level 40).

Inductive step : term -> term -> Type :=
  | Step : forall (r : rule) (c : context) (s : substitution),
             In r system ->
             fill c (substitute s (lhs r)) [>] fill c (substitute s (rhs r))
where "s [>] t" := (step s t).

(* Depth of rule application in rewriting step *)
Definition depth s t (r : s [>] t) : nat :=
  match r with
  | Step _ c _ _ => hole_depth c
  end.

(* Source and target are equal up to the depth of the rewrite step *)
Lemma eq_up_to_rewriting_depth :
  forall `(r : s [>] t) n,
    depth r > n ->
    term_eq_up_to n s t.
Proof.
destruct r.
apply fill_eq_up_to.
Qed.

Reserved Notation "s --> t" (no associativity, at level 40).

Inductive sequence : term -> term -> Type :=
  | Nil   : forall t, t --> t
  | Cons  : forall `(r : s --> t, p : t [>] u), s --> u
  | Lim   : forall s t, (nat -> { t' : term & s --> t' }) -> s --> t
where "s --> t" := (sequence s t).

Implicit Arguments Cons [s t u].

(*
   TODO: the induction principle for sequence misses the IH for
   the Lim case. This happened after introducing the sigma type.

   See also
   http://logical.saclay.inria.fr/coq-puma/messages/82e859ccb67f9ab9
   http://pauillac.inria.fr/cdrom_a_graver/www/coq/mailing-lists/coqclub/0402.html
*)

Fixpoint length `(r : s --> t) : ord' :=
  match r with
  | Nil _          => Zero
  | Cons _ _ r _ _ => Succ (length r)
  | Lim _ _ f      => Limit (fun n => length (projT2 (f n)))
  end.

Fixpoint pref_type `(r : s --> t) : Type :=
  match r with
  | Nil _          => False
  | Cons _ _ r _ _ => (unit + pref_type r) % type
  | Lim _ _ f      => { n : nat & pref_type (projT2 (f n)) }
  end.

Fixpoint pref `(r : s --> t) : pref_type r -> { t' : term & s --> t' } :=
  match r in s --> t return pref_type r -> { t' : term & s --> t' } with
  | Nil _           => !
  | Cons s t' q _ _ => fun i => match i with
                                | inl tt => existT (fun u => s --> u) t' q
                                | inr j  => pref q j
                                end
  | Lim _ _ f       => fun i => match i with
                                | existT n j => pref (projT2 (f n)) j
                                end
  end.

(* maybe this could be a coercion *)
Fixpoint pref_type_as_pred_type `(r : s --> t) : pref_type r -> pred_type (length r) :=
  match r in s --> t return pref_type r -> pred_type (length r) with
  | Nil _          => !
  | Cons _ _ q _ _ => fun i => match i with
                               | inl tt => inl _ tt
                               | inr j  => inr _ (pref_type_as_pred_type q j)
                               end
  | Lim _ _ f      => fun i => match i with
                               | existT n j => existT _ n (pref_type_as_pred_type (projT2 (f n)) j)
                               end
  end.

Implicit Arguments pref_type_as_pred_type [s t r].

Lemma pref_type_as_pred_type_ok :
  forall `(r : s --> t, i : pref_type r),
    length (projT2 (pref r i)) = pred (length r) (pref_type_as_pred_type i).
Proof.
intros s t r i.
induction r as [t| s t r IH u p | s t f].
elim i.
destruct i as [[] | i].
reflexivity.
apply IH.
assert (IH : forall (n : nat) (i : pref_type (projT2 (f n))), length (projT2 (pref (projT2 (f n)) i)) = pred (length (projT2 (f n))) (pref_type_as_pred_type i)).
admit. (* missing IH! *)
destruct i as [n i].
apply IH.
Qed.

Fixpoint pred_type_as_pref_type `(r : s --> t) : pred_type (length r) -> pref_type r :=
  match r in s --> t return pred_type (length r) -> pref_type r with
  | Nil _          => !
  | Cons _ _ q _ _ => fun i => match i with
                               | inl tt => inl _ tt
                               | inr j  => inr _ (pred_type_as_pref_type q j)
                               end
  | Lim _ _ f      => fun i => match i with
                               | existT n j => existT _ n (pred_type_as_pref_type (projT2 (f n)) j)
                               end
  end.

Implicit Arguments pred_type_as_pref_type [s t r].

Lemma pred_type_as_pref_type_ok :
  forall `(r : s --> t, i : pred_type (length r)),
    length (projT2 (pref r (pred_type_as_pref_type i))) = pred (length r) i.
Proof.
intros s t r i.
induction r as [t| s t r IH u p | s t f].
elim i.
destruct i as [[] | i]; simpl.
reflexivity.
apply IH.
assert (IH : forall (n : nat) (i : pred_type (length (projT2 (f n)))), length (projT2 (pref (projT2 (f n)) (pred_type_as_pref_type i))) = pred (length (projT2 (f n))) i).
admit. (* missing IH! *)
destruct i as [n i]; simpl.
apply IH.
Qed.

Lemma pred_type_pref_type_inv :
  forall `(r : s --> t, i : pref_type r),
    i = pred_type_as_pref_type (pref_type_as_pred_type i).
Proof.
intros s t r i.
induction r as [t| s t r IH u p | s t f].
elim i.
destruct i as [[] | i]; simpl; [| rewrite <- (IH i)]; reflexivity.
assert (IH : forall (n : nat) (i : pref_type (projT2 (f n))), i = pred_type_as_pref_type (pref_type_as_pred_type i)).
admit. (* missing IH! *)
destruct i as [n i]; simpl.
rewrite <- (IH n i).
reflexivity.
Qed.

(* Length <=, should be equivalent to ord_le *)
Inductive length_le : forall `(r : s --> t, q : u --> v), Prop :=
  | Length_le_Nil  : forall s `(q : u --> v),
                       Nil s <= q
  | Length_le_Cons : forall `(r : s --> t, q : u --> v, p : t [>] w) i,
                       r <= projT2 (pref q i) ->
                       Cons r p <= q
  | Length_le_Lim  : forall `(f : (nat -> { t' : term & s --> t' }), q : u --> v) t,
                       (forall n, projT2 (f n) <= q) ->
                       Lim t f <= q
where "r <= q" := (length_le r q).

Open Scope ord'_scope.

Require Import Equality.

Lemma length_le_is_ord_le :
  forall `(r : s --> t, q : s --> u),
    r <= q <-> length r <=' length q.
Proof.
induction r; simpl; split; intro H.
constructor.
constructor.
dependent destruction H.
apply Ord'_le_Succ with (pref_type_as_pred_type i).
rewrite <- pref_type_as_pred_type_ok.
apply IHr.
assumption.
inversion_clear H.
apply Length_le_Cons with (pred_type_as_pref_type i).
apply IHr.
rewrite <- pred_type_as_pref_type_ok in H0.
assumption.
assert (IH : forall (n : nat) (u : term) (q : s --> u), projT2 (s0 n) <= q <-> length (projT2 (s0 n)) <=' length q).
admit. (* missing IH! *)
dependent destruction H.
constructor.
intro n.
apply IH.
apply H.
assert (IH : forall (n : nat) (u : term) (q : s --> u), projT2 (s0 n) <= q <-> length (projT2 (s0 n)) <=' length q).
admit. (* missing IH! *)
inversion_clear H.
constructor.
intro n.
apply IH.
apply H0.
Qed.

(* Strict prefix relation *)
Inductive prefix : forall `(r : s --> t, q : s --> u), Prop :=
  Pref : forall `(r : s --> t) i, prefix (projT2 (pref r i)) r.

(* TODO: can we strengthen this lemma to a < instead of <= ? *)
Lemma prefix_length_le :
  forall `(r : s --> t, q : s --> u),
    prefix r q ->
    r <= q.
Proof.
intros.
destruct H as [s t r i].
induction r as [s | s t r IH u p | s t f].
elim i.
assert (H : projT2 (pref (Cons r p) i) <= r).
destruct i as [[] | i]; simpl.
admit. (* by reflexivity of <= *)
apply IH.
admit. (* by ord_le_succ_right equivalent of <= *)
assert (IH : forall (n : nat) (i : pref_type (projT2 (f n))), projT2 (pref (projT2 (f n)) i) <= projT2 (f n)).
admit. (* missing IH! *)
destruct i as [n i].
assert (H : projT2 (pref (projT2 (f n)) i) <= projT2 (f n)).
apply IH.
admit. (* by ord_le_limit_right equivalent of <= *)
Qed.

(*
   'Good' sequences have limit functions f where n < m implies
   that (f n) is a prefix of (f m).
*)
Fixpoint good s t (r : s --> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => good q
  | Lim _ t f      =>
    (forall n, good (projT2 (f n))) /\
    forall n m, (n < m)%nat -> prefix (projT2 (f n)) (projT2 (f m))
  end.

(*
   Weakly convergent sequences have limit functions f where for
   any depth d, from some n, end terms of (f m) with m > n are
   equal up to depth d to the limit term.
*)
Fixpoint weakly_convergent s t (r : s --> t) : Prop :=
  good r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => weakly_convergent q
  | Lim _ t f      =>
    (forall n, weakly_convergent (projT2 (f n))) /\
    forall d, exists n, forall m, (n < m)%nat -> term_eq_up_to d (projT1 (f m)) t
  end.

(* Another try *)
(*
Inductive prefix : forall s t u, (s --> t) -> (s --> u) -> Prop :=
  | PrefNil  : forall `{r : s --> t}, prefix r r
  | PrefCons : forall `{r : s --> t, q : s --> v, p : v [>] u}, prefix r q -> prefix r (Cons q p)
  | PrefLim  : forall `{r : s --> t, q : s --> v, p : nat -> term, f : (forall n : nat, s --> p n), u},
                 (exists n, p n = v /\ f n = q) -> prefix r q -> prefix r (Lim p f u).
*)

Definition Omega := Limit (fun n => n).

(*
Lemma compression :
  trs_left_linear system ->
  forall r : s --> t,
    strongly_convergent r ->
    exists r' : s --> t,
      strongly_convergent r' /\
      length r' <= Omega.
*)

End TRS.
