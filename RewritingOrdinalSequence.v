(* Inductive defintion for rewriting sequences *)

Require Import Prelims.
Require Export List.
Require Export FiniteTerm.
Require Export Term.
Require Export Substitution.
Require Export Context.
Require Export PreOrdinal.
Require Export TermEquality.


Implicit Arguments inl [A].
Implicit Arguments inr [B].

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
Notation fterm := (finite_term F X).
Notation context := (context F X).
Notation substitution := (substitution F X).
Notation trs := (trs F X).

Variable system : trs.

(* Only needed in Coq 8.3 *)
(*Generalizable All Variables.*)

Reserved Notation "s [>] t" (no associativity, at level 40).

Inductive step : term -> term -> Type :=
  | Step : forall (s t : term) (r : rule) (c : context) (u : substitution),
             In r system ->
             fill c (substitute u (lhs r)) [=] s ->
             fill c (substitute u (rhs r)) [=] t ->
             s [>] t
where "s [>] t" := (step s t).

(* Depth of rule application in rewriting step *)
Definition depth s t (p : s [>] t) : nat :=
  match p with
  | Step _ _ _ c _ _ _ _ => hole_depth c
  end.

(* Source and target are equal up to the depth of the rewrite step *)
Lemma eq_up_to_rewriting_depth :
  forall `(p : s [>] t) n,
    n <= depth p ->
    term_eq_up_to n s t.
Proof.
destruct p as [s t r c u Hr Hs Ht].
intros n H.
exact (term_eq_up_to_trans
  (term_eq_up_to_symm (Hs n))
  (term_eq_up_to_trans
    (fill_eq_up_to c (substitute u (lhs r)) (substitute u (rhs r)) H)
    (Ht n))).
Qed.

(* TODO: c' has hole at same position as c *)
Lemma project_match :
  forall (t : term) (c : context) (u : substitution) (f : fterm),
    term_eq_up_to (hole_depth c + pattern_depth f) t (fill c (substitute u f)) ->
    exists c' : context, exists u' : substitution,
      t [=] fill c' (substitute u' f).
Proof.
intros t c u f H.
(* exists (dig t (hole_position c)). *)
Admitted.

(* Normal form if no left-hand side matches *)
Definition normal_form t :=
  ~ exists c:context, exists r, exists u,
    In r system /\ fill c (substitute u (lhs r)) [=] t.

(* TODO: we could use these more generally and move them to Prelims *)
Notation "| s |" := (projT2 s) (no associativity, at level 75).
Notation "$ s $" := (projT1 s) (no associativity, at level 75).

Reserved Notation "s ->> t" (no associativity, at level 40).

(*
   TODO: shouldn't Cons actually ask for bisimilarity?
   | Cons  : forall `(r : s ->> t, p : u [>] v), t [=] u -> s ->> v
*)
Inductive sequence : term -> term -> Type :=
  | Nil   : forall t, t ->> t
  | Cons  : forall `(r : s ->> t, p : t [>] u), s ->> u
  | Lim   : forall s t, (nat -> { t' : term & s ->> t' }) -> s ->> t
where "s ->> t" := (sequence s t).

(*
   Coq ignores the recursive call in the Lim constructor and therefore
   the induction principle is missing a hypothesis. We reset the
   generated induction principle and create a new one below.
*)
Reset sequence_rect.

Notation "s ->> t" := (sequence s t).
Implicit Arguments Cons [s t u].

Section InductionPrinciple.

Variable P : forall `(r : s ->> t), Type.

Hypothesis H1 : forall t, P (Nil t).

Hypothesis H2 :
  forall `(r : s ->> t, p : t [>] u),
    P r ->
    P (Cons r p).

Hypothesis H3 :
  forall s t (f : nat -> {t' : term &  s ->> t'}),
    (forall n, P (|f n|) ) ->
    P (Lim t f).

Fixpoint sequence_rect `(r : s ->> t) : P r :=
  match r return P r with
  | Nil t          => H1 t
  | Cons s t r u p => H2 p (sequence_rect r)
  | Lim s t f      => H3 t f (fun n => sequence_rect (|f n|))
  end.

End InductionPrinciple.

Definition sequence_ind (P : `(s ->> t -> Prop)) :=
  sequence_rect P.

Definition cons_term_eq `(r : s ->> t, p : u [>] v) : u [=] t -> s ->> v :=
  match p in u [>] v return u [=] t -> s ->> v with
  | Step u v rul c sub Hr Hs Ht =>
      fun H => Cons r (Step rul c sub Hr (term_eq_trans Hs H) Ht)
  end.

Fixpoint length `(r : s ->> t) : ord' :=
  match r with
  | Nil _          => Zero
  | Cons _ _ r _ _ => Succ (length r)
  | Lim _ _ f      => Limit (fun n => length (|f n|))
  end.

Lemma length_limit_discriminate :
  forall `(r : s ->> t) f,
    length r = Limit f ->
    exists g, r = Lim t g.
Proof.
intros s t [| | u v g] f H.
discriminate H.
discriminate H.
exists g; reflexivity.
Qed.

Fixpoint pref_type `(r : s ->> t) : Type :=
  match r with
  | Nil _          => False
  | Cons _ _ r _ _ => (unit + pref_type r) % type
  | Lim _ _ f      => { n : nat & pref_type (|f n|) }
  end.

Fixpoint pref_term `(r : s ->> u) : pref_type r -> term :=
  match r in s ->> u return pref_type r -> term with
  | Nil _          => !
  | Cons s t q _ _ => fun i => match i with
                               | inl tt => t
                               | inr j  => pref_term q j
                               end
  | Lim _ _ f      => fun i => match i with
                               | existT n j => pref_term (|f n|) j
                               end
  end.

Fixpoint pref_term_next `(r : s ->> u) : pref_type r -> term :=
  match r in s ->> u return pref_type r -> term with
  | Nil _          => !
  | Cons s t q _ _ => fun i => match i with
                               | inl tt => u
                               | inr j  => pref_term_next q j
                               end
  | Lim _ _ f      => fun i => match i with
                               | existT n j => pref_term_next (|f n|) j
                               end
  end.

Fixpoint pref `(r : s ->> u) : forall i : pref_type r, s ->> pref_term r i :=
  match r in s ->> u return forall i : pref_type r, s ->> pref_term r i with
  | Nil _          => fun i => ! i
  | Cons s t q _ _ => fun i => match i with
                               | inl tt => q
                               | inr j  => pref q j
                               end
  | Lim _ _ f      => fun i => match i with
                               | existT n j => pref (|f n|) j
                               end
  end.

Fixpoint pref_step `(r : s ->> u) : forall i : pref_type r, pref_term r i [>] pref_term_next r i :=
  match r in s ->> u return forall i : pref_type r, pref_term r i [>] pref_term_next r i with
  | Nil _          => fun i => ! i
  | Cons s t q _ p => fun i => match i with
                               | inl tt => p
                               | inr j  => pref_step q j
                               end
  | Lim _ _ f      => fun i => match i with
                               | existT n j => pref_step (|f n|) j
                               end
  end.

(* maybe this could be a coercion *)
Fixpoint pref_type_as_pred_type `(r : s ->> t) : pref_type r -> pred_type (length r) :=
  match r in s ->> t return pref_type r -> pred_type (length r) with
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
  forall `(r : s ->> t, i : pref_type r),
    length (pref r i) = pred (length r) (pref_type_as_pred_type i).
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

Fixpoint pred_type_as_pref_type `(r : s ->> t) : pred_type (length r) -> pref_type r :=
  match r in s ->> t return pred_type (length r) -> pref_type r with
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
  forall `(r : s ->> t, i : pred_type (length r)),
    length (pref r (pred_type_as_pref_type i)) = pred (length r) i.
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
  forall `(r : s ->> t, i : pref_type r),
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

(* Embeddings of reductions
   Idea by Vincent, this is all still a very rough try *)
Inductive embed : forall `(r : s ->> t, q : u ->> v), Prop :=
  | Embed_Nil  : forall s `(q : u ->> v),
                   Nil s <= q
  | Embed_Cons : forall `(q : u ->> v, r : s ->> pref_term q i),
                   r <= (pref q i) ->
                   Cons r (pref_step q i) <= q
  | Embed_Lim  : forall `(f : (nat -> { t' : term & s ->> t' }), q : u ->> v) t,
                   (forall n, (|f n|) <= q) ->
                   Lim t f <= q
where "r <= q" := (embed r q).

Definition embed_strict `(r : s ->> t, q : u ->> v) := exists i, r <= pref q i.
Infix " < " := embed_strict (no associativity, at level 70).

Open Scope ord'_scope.

(* TODO: figure out what to import exactly (Equality imports PI axiom) *)
Require Import Equality.

Lemma embed_length :
  forall `(r : s ->> t, q : u ->> v),
    r <= q -> length r <=' length q.
Proof.
induction r as [t | s t r w p IH | s t f IH]; simpl; intros u v q H.
constructor.
dependent destruction H.
apply Ord'_le_Succ with (pref_type_as_pred_type i).
rewrite <- pref_type_as_pred_type_ok.
apply (IH u (pref_term q i) (pref q i)).
assumption.
dependent destruction H.
constructor.
intro n.
apply (IH n u v q).
apply H.
Qed.

Lemma embed_lim_right :
  forall `(r : s ->> t, f : (nat -> { v' : term & u ->> v' })) v n,
    r <= (|f n|) ->
    r <= Lim v f.
Proof.
induction r as [t | s t r w p _ | s t f IH]; intros u g v n H.
constructor.
dependent destruction H.
(*apply Embed_Cons with (q := Lim v g) (i := existT (fun n => pref_type (|g n|)) n i).*)
apply (@Embed_Cons u v (Lim v g) s (existT (fun n => pref_type (|g n|)) n i) r).
assumption.
constructor.
intro m.
apply (IH m u g v n).
dependent destruction H.
trivial.
Qed.

Lemma embed_refl :
  forall `(r : s ->> t), r <= r.
Proof.
induction r as [t | s t r u p IH | s t f IH].
constructor.
apply Embed_Cons with (q := Cons r p) (i := inl (pref_type r) tt).
assumption.
constructor.
intro n.
apply embed_lim_right with n.
apply IH.
Qed.

Lemma embed_cons_left :
  forall `(r : s ->> t, q : v ->> w, p : t [>] u),
    Cons r p <= q ->
    r <= q.
Proof.
intros.
admit.
Qed.

(* Strict prefix relation *)
(*
   NOTE: the problem described below is not valid, because
   prefixes of (Lim f) are not (f n), but prefixes of (f n).
   I.e., pref_type (Lim f) = { n : nat & pref_type (|f n|) }.
*)
(*
   Consider a TRS with rule

     ABA : A -> B(A)

   i.e. the one in Examples.v, and omega-step reduction

     A ->> B(B(B(...)))

   This reduction can be defined by

     Lim f : A ->> B(B(B(...)))

   where

     f 0  = Nil
     f Sn = Cons (Cons (f n) [ABA]) [ABA]

   i.e. f Sn has two more steps than f n.

   Now, take any prefix of this reduction of odd length. It is not
   a prefix of Lim f by the definition below.

   This is also Hancock's reason not to use pred directly as an
   order relation.

   I still think it would be best to define some order analoguous
   to ord_le, but I don't see an obvious way to do this.
*)
Inductive prefix : forall `(r : s ->> t, q : s ->> u), Prop :=
  Pref : forall `(r : s ->> t) i, prefix (pref r i) r.

Lemma prefix_length_lt :
  forall `(r : s ->> t, q : s ->> u),
    prefix r q ->
    exists i, r <= (pref q i).
Proof.
destruct 1 as [s t r i].
exists i.
apply embed_refl.
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

(*
Fixpoint pref_trans `(r : s ->> t)  : forall i : pref_type r, pref_type (|pref r i|) -> pref_type r :=
  match r in s ->> t return forall i : pref_type r, pref_type (|pref r i|) -> pref_type r with
  | Nil _ => fun i j => i
  | Cons _ _ r' _ p => fun i =>
    match i as k return k = i -> pref_type (|pref (Cons r' p) k|) -> pref_type (Cons r' p) with
    | inl tt => fun H j => inr unit j
    | inr i' => fun H j => inr _ (pref_trans r' i' j)
    end refl_equal
  | Lim _ _ f => fun i =>
    match i with
    | existT n i' => fun j => existT _ n (pref_trans (|f n|) i' j)
    end
  end.
*)

(* TODO: since the change of pref to not return a sigma type, we must use
   JMeq here, if we revert that we can again use coq equality *)
Lemma pref_trans :
  forall `(r : s ->> t, i : pref_type r, j : pref_type (pref r i)),
    exists k : pref_type r, JMeq (pref r k) (pref (pref r i) j).
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

Implicit Arguments pref_trans [s t r].

Lemma prefix_trans :
  forall `(r : s ->> t, q : s ->> u, o : s ->> v),
    prefix r q ->
    prefix q o ->
    prefix r o.
Proof.
intros.
destruct H.
destruct H0.
destruct (pref_trans i0 i).
(*
rewrite <- H.
constructor.
*)
admit.
Qed.

(*
   'Good' sequences have limit functions f where n < m implies
   that (f n) is strictly embedded in (f m).
*)
Fixpoint good `(r : s ->> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => good q
  | Lim _ t f      =>
    (forall n, good (|f n|)) /\
    forall n m, (n < m)%nat -> (|f n|) < (|f m|)
  end.

Fixpoint weakly_convergent `(r : s ->> t) : Prop :=
  good r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => weakly_convergent q
  | Lim _ t f      =>
    (forall n, weakly_convergent (|f n|)) /\
    forall d, exists i, forall j,
      pref r i <= pref r j ->   (* prefix (|pref r i|) (|pref r j|) -> *)
      term_eq_up_to d (pref_term r j) t
  end.

Fixpoint strongly_convergent `(r : s ->> t) : Prop :=
  weakly_convergent r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => strongly_convergent q
  | Lim _ t f      =>
    (forall n, strongly_convergent (|f n|)) /\
    forall d, exists i, forall j,
      pref r i <= pref r j ->
      (depth (pref_step r j) > d)%nat
  end.

(*
   Weakly convergent sequences have limit functions f where for
   any depth d, from some n, end terms of (f m) with m > n are
   equal up to depth d to the limit term.
*)
(*
Fixpoint weakly_convergent `(r : s ->> t) : Prop :=
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
(*
Fixpoint weakly_convergent `(r : s ->> t) : Prop :=
  good r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => weakly_convergent q
  | Lim _ t f      =>
    (forall n, weakly_convergent (|f n|)) /\
    forall d, exists i, forall j,
      (|pref r i|) <= (|pref r j|) ->   (* prefix (|pref r i|) (|pref r j|) -> *)
      term_eq_up_to d ($ pref r j $) t
  end.

Definition step_below d `(r : s ->> t) : Prop :=
  match r with
  | Cons _ _ _ _ p => (depth p > d)%nat
  | _              => True
  end.

(* TODO: is this strong convergence? *)
Fixpoint strongly_convergent `(r : s ->> t) : Prop :=
  weakly_convergent r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => strongly_convergent q
  | Lim _ t f      =>
    (forall n, strongly_convergent (|f n|)) /\
    forall d, exists i, forall j,
      (|pref r i|) <= (|pref r j|) ->
      step_below d (|pref r j|)
  end.
*)

Lemma aaa :
  forall s t f c l sigma,
    strongly_convergent (Lim t f : s ->> t) ->
    t [=] fill c (substitute sigma l) ->
    exists i : pref_type (Lim t f),
      exists tau,
        (pref_term (Lim t f) i) [=] fill c (substitute tau l).
Proof.
intros s t f c l sigma sc H.
destruct sc as [[_ [_ wc]] [_ _]].
destruct (wc (hole_depth c + pattern_depth l)) as [i Hi].
exists i.
assert (H1 : term_eq_up_to (hole_depth c + pattern_depth l) (pref_term (Lim t f) i) t).
apply Hi.
admit.
Admitted.

Lemma bbb :
  forall c (l : finite_term F X) sigma s,
    term_eq_up_to (hole_depth c + pattern_depth l) s (fill c (substitute sigma l)) ->
    exists d, exists tau,
      s [=] fill d (substitute tau l).
Admitted.

(* TODO: why is jmeq_refl needed here, and can we write it ourselves? *)
(*
Program Fixpoint program_append `(r : s ->> t, q : t ->> u) : s ->> u :=
  match q with
  | Nil t0         => r
  | Cons _ _ q _ p => Cons (program_append r q) p
  | Lim _ u f      => Lim u (fun o => existT (fun u => s ->> u) ($ f o $) (program_append r (|f o|)))
  end.
*)

(* yes we can *)
Fixpoint append_rec (s t u : term) (q : t ->> u) : s ->> t -> s ->> u :=
  match q in t ->> u return s ->> t -> s ->> u with
  | Nil t0         => fun r => r
  | Cons _ _ q _ p => fun r => Cons (append_rec q r) p
  | Lim _ u f      => fun r => Lim u (fun o => existT (fun u => s ->> u) ($ f o $) (append_rec (|f o|) r))
  end.

Definition append `(r : s ->> t, q : t ->> u) : s ->> u := append_rec q r.

Lemma append_length :
  forall `(r : s ->> t, q : t ->> u),
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

Lemma compression :
  trs_left_linear system ->
  forall `(r : s ->> t),
    strongly_convergent r ->
    exists r' : s ->> t,
      strongly_convergent r' /\
      length r' <=' Omega.
Proof.
intros LL s t r SC.
induction r as [t | s t r u p IH | s t f IH].

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


Implicit Arguments normal_form [F X system].
