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
(*Generalizable All Variables.*)

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

(* TODO: we could use these more generally and move them to Prelims *)
Notation "| s |" := (projT2 s) (no associativity, at level 75).
Notation "$ s $" := (projT1 s) (no associativity, at level 75).

Reserved Notation "s --> t" (no associativity, at level 40).

Inductive sequence : term -> term -> Type :=
  | Nil   : forall t, t --> t
  | Cons  : forall `(r : s --> t, p : t [>] u), s --> u
  | Lim   : forall s t, (nat -> { t' : term & s --> t' }) -> s --> t
where "s --> t" := (sequence s t).

(*
   Coq ignores the recursive call in the Lim constructor and therefore
   the induction principle is missing a hypothesis. We reset the
   generated induction principle and create a new one below.
*)
Reset sequence_rect.

Notation "s --> t" := (sequence s t).
Implicit Arguments Cons [s t u].

Section InductionPrinciple.

Variable P : forall `(r : s --> t), Type.

Hypothesis H1 : forall t, P (Nil t).

Hypothesis H2 :
  forall `(r : s --> t, p : t [>] u),
    P r ->
    P (Cons r p).

Hypothesis H3 :
  forall s t (f : nat -> {t' : term &  s --> t'}),
    (forall n, P (|f n|) ) ->
    P (Lim t f).

Fixpoint sequence_rect `(r : s --> t) : P r :=
  match r return P r with
  | Nil t          => H1 t
  | Cons s t r u p => H2 p (sequence_rect r)
  | Lim s t f      => H3 t f (fun n => sequence_rect (|f n|))
  end.

End InductionPrinciple.

Definition sequence_ind (P : `(s --> t -> Prop)) :=
  sequence_rect P.

Fixpoint length `(r : s --> t) : ord' :=
  match r with
  | Nil _          => Zero
  | Cons _ _ r _ _ => Succ (length r)
  | Lim _ _ f      => Limit (fun n => length (|f n|))
  end.

Fixpoint pref_type `(r : s --> t) : Type :=
  match r with
  | Nil _          => False
  | Cons _ _ r _ _ => (unit + pref_type r) % type
  | Lim _ _ f      => { n : nat & pref_type (|f n|) }
  end.

Fixpoint pref `(r : s --> t) : pref_type r -> { t' : term & s --> t' } :=
  match r in s --> t return pref_type r -> { t' : term & s --> t' } with
  | Nil _           => !
  | Cons s t' q _ _ => fun i => match i with
                                | inl tt => existT (fun u => s --> u) t' q
                                | inr j  => pref q j
                                end
  | Lim _ _ f       => fun i => match i with
                                | existT n j => pref (|f n|) j
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
                               | existT n j => existT _ n (pref_type_as_pred_type (|f n|) j)
                               end
  end.

Implicit Arguments pref_type_as_pred_type [s t r].

Lemma pref_type_as_pred_type_ok :
  forall `(r : s --> t, i : pref_type r),
    length (|pref r i|) = pred (length r) (pref_type_as_pred_type i).
Proof.
intros s t r i.
induction r as [t| s t r u p IH | s t f IH ].
elim i.
destruct i as [[] | i].
reflexivity.
apply IH.
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
                               | existT n j => existT _ n (pred_type_as_pref_type (|f n|) j)
                               end
  end.

Implicit Arguments pred_type_as_pref_type [s t r].

Lemma pred_type_as_pref_type_ok :
  forall `(r : s --> t, i : pred_type (length r)),
    length (|pref r (pred_type_as_pref_type i)|) = pred (length r) i.
Proof.
intros s t r i.
induction r as [t| s t r u p IH | s t f IH].
elim i.
destruct i as [[] | i]; simpl.
reflexivity.
apply IH.
destruct i as [n i]; simpl.
apply IH.
Qed.

Lemma pred_type_pref_type_inv :
  forall `(r : s --> t, i : pref_type r),
    i = pred_type_as_pref_type (pref_type_as_pred_type i).
Proof.
intros s t r i.
induction r as [t| s t r u p IH | s t f IH].
elim i.
destruct i as [[] | i]; simpl; [| rewrite <- (IH i)]; reflexivity.
destruct i as [n i]; simpl.
rewrite <- (IH n i).
reflexivity.
Qed.

(* Length <=, should be equivalent to ord_le *)
Inductive length_le : forall `(r : s --> t, q : u --> v), Prop :=
  | Length_le_Nil  : forall s `(q : u --> v),
                       Nil s <= q
  | Length_le_Cons : forall `(r : s --> t, q : u --> v, p : t [>] w) i,
                       r <= (|pref q i|) ->
                       Cons r p <= q
  | Length_le_Lim  : forall `(f : (nat -> { t' : term & s --> t' }), q : u --> v) t,
                       (forall n, (|f n|) <= q) ->
                       Lim t f <= q
where "r <= q" := (length_le r q).

Open Scope ord'_scope.

Require Import Equality.

Lemma length_le_is_ord_le :
  forall `(r : s --> t, q : u --> v),
    r <= q <-> length r <=' length q.
Proof.
induction r as [t| s t r u p IH | s t f IH]; simpl; split; intro H.
constructor.
constructor.
dependent destruction H.
apply Ord'_le_Succ with (pref_type_as_pred_type i).
rewrite <- pref_type_as_pred_type_ok.
apply (IH u ($ pref q i $) (| pref q i |)). (* apply IH. *)
assumption.
inversion_clear H.
apply Length_le_Cons with (pred_type_as_pref_type i).
apply (IH u0 ($ pref q (pred_type_as_pref_type i) $) (| pref q (pred_type_as_pref_type i) |)). (* apply IH. *)
rewrite <- pred_type_as_pref_type_ok in H0.
assumption.
dependent destruction H.
constructor.
intro n.
apply (IH n u v q). (* apply IH. *)
apply H.
inversion_clear H.
constructor.
intro n.
apply (IH n u v q). (* apply IH. *)
apply H0.
Qed.

Lemma length_le_refl :
  forall `(r : s --> t), r <= r.
Proof.
intros.
apply (length_le_is_ord_le r r).
apply ord'_le_refl.
Qed.

(* Strict prefix relation *)
Inductive prefix : forall `(r : s --> t, q : s --> u), Prop :=
  Pref : forall `(r : s --> t) i, prefix (|pref r i|) r.

Lemma prefix_length_lt :
  forall `(r : s --> t, q : s --> u),
    prefix r q ->
    exists i, r <= (|pref q i|).
Proof.
destruct 1 as [s t r i].
exists i.
apply length_le_refl.
Qed.

Lemma pred_trans :
  forall alpha i j,
    exists k, pred alpha k = pred (pred alpha i) j.
Proof.
induction alpha as [| alpha IH | f IH]; intros.
elim i.
destruct i as [[] | i]; simpl in j |- *.
exists (inr _ j).
reflexivity.
destruct (IH i j) as [k H].
exists (inr _ k).
assumption.
destruct i as [n i]; simpl in j |- *.
destruct (IH n i j) as [k H].
exists (existT (fun n => pred_type (f n)) n k).
assumption.
Qed.

Fixpoint pref_trans `(r : s --> t)  : forall i : pref_type r, pref_type (|pref r i|) -> pref_type r :=
  match r in s --> t return forall i : pref_type r, pref_type (|pref r i|) -> pref_type r with
  | Nil _ => fun i j => i 
  | Cons _ _ r' _ p => fun i => 
    match i as k return k = i -> pref_type (|pref (Cons r' p) k|) -> pref_type (Cons r' p) with 
    | inl tt => fun H j => inr unit j
    | inr i' => fun H j => inr _ (pref_trans r' i' j)
    end (refl_equal i)
  | Lim _ _ f => fun i =>
    match i with 
    | existT n i' => fun j => existT _ n (pref_trans (|f n|) i' j)
    end
  end.

Require Import Eqdep.

Lemma lemma : 
   forall `(r : s --> t , i : pref_type r, j : pref_type (|pref r i|) ),
   JMeq (|pref r (pref_trans r i j)|) (|pref (|pref r i|) j|).
Admitted.

Lemma lemma2 : 
   forall `(r : s --> t , i : pref_type r, j : pref_type (|pref r i|) ),
   prefix (|pref r (pref_trans r i j)|) r ->
   prefix (|pref (|pref r i|) j|) r.
Proof.
intros s t r i j H.
assert (H0 := lemma r i j).
dependent destruction H0.
rewrite H0 in H1.



exact H.
induction r.
intros [].
intros [[]|i']; simpl.
intros j H.
exact H.
change (pref_type r) in i'.
intros j H.

assert (Z := IHr i' j).

dependent destruction H.
simpl in i.
destruct i.
destruct u.

change (prefix (|pref (|pref (Cons r p) (inr _ i') |) j |) (Cons r p)).

destruct (IHr i' j).
constructor.
*)



(*
Lemma pref_trans :
  forall `(r : s --> t, i : pref_type r, j : pref_type (|pref r i|)),
    exists k : pref_type r, JMeq (|pref r k|) (|pref (|pref r i|) j|).
Proof.
induction r; intros.
elim i.
destruct i as [[] | i]; simpl in j |- *.
exists (inr _ j).
reflexivity.
destruct (IHr i j) as [k H].
exists (inr _ k).
assumption.
destruct i as [n i]; simpl in j |- *.
destruct (H n i j) as [k H1].
exists (existT (fun n => pref_type (|f n|)) n k).
assumption.
Qed.
*)

Implicit Arguments pref_trans [s t r].

Lemma prefix_trans :
  forall `(r : s --> t, q : s --> u, o : s --> v),
    prefix r q ->
    prefix q o ->
    prefix r o.
Proof.
intros.
destruct H.
destruct H0.
apply lemma.
constructor.
destruct (pref_trans i0 i).
inversion H.

Print Pref.

dependent destruction H.


generalize H0.
clear H0.

dependent rewrite H.




apply (Pref r x).

assert (G := JMeq_eq H).
(*rewrite <- H.*)
(*assert (JMeq_eq H).*)

(*
intros.
destruct H.
destruct H0.
induction r.
elim i0.
destruct i0 as [[] | i0]; simpl in i |- *.
change (prefix (projT2 (pref (Cons r p) (inr _ i))) (Cons r p)).
constructor.
assert (H : prefix (projT2 (pref (projT2 (pref r i0)) i)) r).
apply IHr.
change (prefix (|pref (|pref (Cons r p) (inr _ i0) |) i |) (Cons r p)).
dependent destruction H.
(*rewrite <- x.*)
*)
Admitted.

(*
   'Good' sequences have limit functions f where n < m implies
   that (f n) is a prefix of (f m).
*)
Fixpoint good `(r : s --> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => good q
  | Lim _ t f      =>
    (forall n, good (|f n|)) /\
    forall n m, (n < m)%nat -> prefix (|f n|) (|f m|)
  end.

(*
   Weakly convergent sequences have limit functions f where for
   any depth d, from some n, end terms of (f m) with m > n are
   equal up to depth d to the limit term.
*)
(*
Fixpoint weakly_convergent `(r : s --> t) : Prop :=
  good r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => weakly_convergent q
  | Lim _ t f      =>
    (forall n, weakly_convergent (|f n|)) /\
    forall d, exists n, forall m, (n < m)%nat -> term_eq_up_to d ($ f m $) t
  end.
*)
(*
   The commented-out definition for weak convergence above is not strong
   enough: (f m) and (f m+1) might differ more than one step, so we are
   not done by just checking the end terms for all (f m).

   In the alternative definition below, it is stated that the end terms
   of all prefixes of such an (f m) having at leas length (f n) should be
   equal to t up to depth d.
*)
Fixpoint weakly_convergent `(r : s --> t) : Prop :=
  good r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => weakly_convergent q
  | Lim _ t f      =>
    (forall n, weakly_convergent (|f n|)) /\
    forall d, exists n, forall m, (n < m)%nat -> forall i,
      (|f n|) <= (|pref (|f m|) i|) ->
      term_eq_up_to d ($ pref (|f m|) i $) t
  end.

Definition last_step_below d `(r : s --> t) : Prop :=
  match r with
  | Cons _ _ _ _ p => (depth p > d)%nat
  | _              => True
  end.

(* TODO: is this strong convergence? *)
Fixpoint strongly_convergent `(r : s --> t) : Prop :=
  weakly_convergent r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => strongly_convergent q
  | Lim _ t f      =>
    (forall n, strongly_convergent (|f n|)) /\
    forall d, exists n, forall m, (n < m)%nat -> forall i,
      (|f n|) <= (|pref (|f m|) i|) ->
      last_step_below d (|pref (|f m|) i|)
  end.

(* TODO: why is jmeq_refl needed here, and can we write it ourselves? *)

Program Fixpoint program_append `(r : s --> t, q : t --> u) : s --> u :=
  match q with
  | Nil t0         => r
  | Cons _ _ q _ p => Cons (program_append r q) p
  | Lim _ u f      => Lim u (fun o => existT (fun u => s --> u) ($ f o $) (program_append r (|f o|)))
  end.

Print program_append.

(* yes we can *)

Fixpoint append_rec (s t u : term) (q : t --> u) : s --> t -> s --> u :=
  match q in t --> u return s --> t -> s --> u with
  | Nil t0         => fun r => r
  | Cons _ _ q _ p => fun r => Cons (append_rec q r) p
  | Lim _ u f      => fun r => Lim u (fun o => existT (fun u => s --> u) ($ f o $) (append_rec (|f o|) r))
  end.

Definition append `(r : s --> t, q : t --> u) : s --> u := append_rec q r.

Lemma append_length :
  forall `(r : s --> t, q : t --> u),
    length (append r q) ==' add (length r) (length q).
Proof.
induction q as [u| t u q v p IH | t u f IH]; simpl.
apply ord'_eq_refl.
split.
apply Ord'_le_Succ with (inl (pred_type (add (length r) (length q))) tt).
apply (IH r).
apply Ord'_le_Succ with (inl (pred_type (length (append r q))) tt).
apply (IH r).
split; constructor; intro n; apply ord'_le_limit_right with n; apply (IH n r).
Qed.

Definition Omega := Limit (fun n => n).

Lemma ord'_le_omega_elim :
  forall alpha,
    alpha <=' Omega ->
    alpha <' Omega \/ alpha ==' Omega.
Proof.
intros alpha H. unfold ord'_lt.
induction alpha as [| alpha IH | f IH].
left.
exists (existT (fun (n:nat) => pred_type n) 1 (inl _ tt)).
constructor.
left.
destruct IH as [[[n j] H1] | H1].
apply (ord'_le_succ_left H).
simpl in H1.
exists (existT (fun (n:nat) => pred_type n) (S n) (inl _ tt)); simpl.
destruct n as [| n].
elim j.
destruct j as [[] | j]; simpl in H1; apply ord'_le_succ_intro.
assumption.
apply ord'_le_pred_right with j.
assumption.
contradiction ord'_le_not_pred_right_strong with (Succ alpha) Omega (inl (pred_type alpha) tt).
apply H1.
right.
split.
assumption.
constructor.
(* i guess we use monotonicity of f here, otherwise we loose... *)
Admitted.

(* TODO: for things like this, I think we need another equality on ordinals *)
Lemma ord'_le_omega_elim' :
  forall alpha,
    alpha <=' Omega ->
    alpha <' Omega \/ alpha = Omega.
Proof.
intros alpha H. unfold ord'_lt.
induction alpha as [| alpha IH | f IH].
left.
exists (existT (fun (n:nat) => pred_type n) 1 (inl _ tt)).
constructor.
left.
destruct IH as [[[n j] H1] | H1].
apply (ord'_le_succ_left H).
simpl in H1.
exists (existT (fun (n:nat) => pred_type n) (S n) (inl _ tt)); simpl.
destruct n as [| n].
elim j.
destruct j as [[] | j]; simpl in H1; apply ord'_le_succ_intro.
assumption.
apply ord'_le_pred_right with j.
assumption.
rewrite H1 in H.
contradiction ord'_le_not_succ with Omega.
right.
apply f_equal.
(* We cannot prove this *)
Admitted.

Lemma compression :
  trs_left_linear system ->
  forall `(r : s --> t),
    strongly_convergent r ->
    exists r' : s --> t,
      strongly_convergent r' /\
      length r' <=' Omega.
Proof.
intros LL s t r SC.
induction r as [t| s t r u p IH | s t f IH].

(* Case (Nil t) *)
exists (Nil t).
split.
trivial.
apply Ord'_le_Zero.

(* Case (Cons r p) *)
assert (IH' := (IH (proj2 SC))); clear r SC IH.
destruct IH' as [r [SC IH]].
destruct (ord'_le_omega_elim IH) as [[i H] | H]; clear IH.
exists (Cons r p).
split.
admit. (* apply SCr'. *)
apply Ord'_le_Succ with i.
assumption.
admit.

(* Case (Lim t f) *)
admit.
Qed.

End TRS.
