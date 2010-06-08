(* Inductive defintion for rewriting sequences *)


Require Import Prelims.
Require Export List.
Require Export FiniteTerm.
Require Export Term.
Require Export Substitution.
Require Export Context.
Require Export PreOrdinal.
Require Export TermEquality.

(* TODO: figure out what to import exactly (Equality imports PI axiom) *)
Require Import Equality.


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
Generalizable All Variables.

Reserved Notation "s [>] t" (no associativity, at level 40).

Inductive step : term -> term -> Type :=
  | Step : forall (s t : term) (r : rule) (c : context) (u : substitution),
             In r system ->
             fill c (substitute u (lhs r)) [~] s ->
             fill c (substitute u (rhs r)) [~] t ->
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
  (term_eq_up_to_symm ((term_bis_implies_term_eq Hs) n))
  (term_eq_up_to_trans
    (fill_eq_up_to c (substitute u (lhs r)) (substitute u (rhs r)) H)
    ((term_bis_implies_term_eq Ht) n))).
Qed.

Lemma project_match :
  forall (t : term) (c : context) (u : substitution) (f : fterm),
    term_eq_up_to (hole_depth c + pattern_depth f) t (fill c (substitute u f)) ->
    exists c' : context, exists u' : substitution,
      t [=] fill c' (substitute u' f) /\
      hole_position c = hole_position c'.
Proof.
intros t c u f H.
(* exists (dig t (hole_position c)). *)
Admitted.

(* Normal form if no left-hand side matches *)
Definition normal_form t :=
  ~ exists c:context, exists r, exists u,
    In r system /\ fill c (substitute u (lhs r)) [~] t.

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

Definition cons_term_bis `(r : s ->> t, p : u [>] v) : u [~] t -> s ->> v :=
  match p in u [>] v return u [~] t -> s ->> v with
  | Step u v rul c sub Hr Hs Ht =>
      fun H => Cons r (Step rul c sub Hr (term_bis_trans Hs H) Ht)
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

Fixpoint pref `(r : s ->> t) :
  pref_type r -> { ts : (term * term)%type & ((s ->> (fst ts)) * ((fst ts) [>] (snd ts)))%type } :=
  match r in s ->> t return pref_type r -> { ts : (term * term)%type & ((s ->> (fst ts)) * ((fst ts) [>] (snd ts)))%type } with
  | Nil _           => !
  | Cons s t' q u p => fun i => match i with
                                  (* TODO: i would like t instead of u here *)
                                | inl tt => existT (fun ts => (s ->> fst ts) * (fst ts [>] snd ts))%type (t', u) (q, p)
                                | inr j  => pref q j
                                end
  | Lim _ _ f       => fun i => match i with
                                | existT n j => pref (|f n|) j
                                end
  end.

Lemma pref_trans :
  forall `(r : s ->> t, i : pref_type r, j : pref_type (fst (| pref r i |))),
    exists k : pref_type r, pref r k = pref (fst (| pref r i |)) j.
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
    length (fst (|pref r i|)) = pred (length r) (pref_type_as_pred_type i).
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
    length (fst (|pref r (pred_type_as_pref_type i)|)) = pred (length r) i.
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
(* TODO: maybe should Nil s <= q only hold for q : s ->> _ ? *)
Inductive embed : forall `(r : s ->> t, q : u ->> v), Prop :=
  | Embed_Nil  : forall s `(q : u ->> v),
                   Nil s <= q
  | Embed_Cons : forall `(q : u ->> v, r : s ->> (fst ($ pref q i $))),
                   r <= (fst (| pref q i |)) ->
                   Cons r (snd (| pref q i |)) <= q
  | Embed_Lim  : forall `(f : (nat -> { t' : term & s ->> t' }), q : u ->> v) t,
                   (forall n, (|f n|) <= q) ->
                   Lim t f <= q
where "r <= q" := (embed r q).

Definition embed_strict `(r : s ->> t, q : u ->> v) := exists i, r <= fst (| pref q i |).
Infix " < " := embed_strict (no associativity, at level 70).

Open Scope ord'_scope.

Lemma embed_length :
  forall `(r : s ->> t, q : u ->> v),
    r <= q -> length r <=' length q.
Proof.
induction r as [t | s t r w p IH | s t f IH]; simpl; intros u v q H.
constructor.
dependent destruction H.
apply Ord'_le_Succ with (pref_type_as_pred_type i).
rewrite <- pref_type_as_pred_type_ok.
apply (IH u (fst ($ pref q i $)) (fst (| pref q i |))).
assumption.
dependent destruction H.
constructor.
intro n.
apply (IH n u v q).
apply H.
Qed.

Lemma embed_pref_right :
  forall `(r : s ->> t, q : u ->> v, i : pref_type q),
    r <= fst (| pref q i |) ->
    r <= q.
Proof.
induction r as [t | s t r w p IH | s t f IH]; intros u v q i H.
constructor.
dependent destruction H.
destruct (pref_trans i i0) as [k T].
revert r IH H.
rewrite <- T.
intros r IH H.
apply Embed_Cons.
assumption.
constructor.
intro n.
dependent destruction H.
apply IH with i.
trivial.
Qed.

Lemma embed_pref_left :
  forall `(r : s ->> t, q : u ->> v, i : pref_type r),
    r <= q ->
    fst (|pref r i|) <= q.
Proof.
intros s t r u v q i H.
induction H as [s u v q | u v q s j r H IH | s f u v q t H IH].
elim i.
destruct i as [[] | i]; apply embed_pref_right with j.
apply H.
apply IH.
destruct i.
apply IH.
Qed.

Lemma embed_not_cons_nil :
  forall `(r : s ->> t, p : t [>] u) v,
    ~ Cons r p <= Nil v.
Proof.
intros s t r u p v H.
dependent destruction H.
destruct i.
Qed.

Lemma embed_cons_elim :
  forall `(r : s ->> t, q : u ->> v, p : t [>] w, o : v [>] x),
    Cons r p <= Cons q o ->
    r <= q.
Proof.
intros s t r u v q w p x o H.
dependent destruction H.
destruct i as [[] |]; [| apply embed_pref_right with p]; assumption.
Qed.

Lemma first_pref_after_cons_id :
  forall `(r : s ->> t, p : t [>] u),
    r = fst (|pref (Cons r p) (inl (pref_type r) tt)|).
Proof.
trivial.
Qed.

Lemma embed_cons_left :
  forall `(r : s ->> t, q : v ->> w, p : t [>] u),
    Cons r p <= q ->
    r <= q.
Proof.
intros s t r v w q u p H.
rewrite (first_pref_after_cons_id r) with p.
apply (@embed_pref_left s u (Cons r p) v w q (inl (pref_type r) tt)).
assumption.
Qed.

Lemma embed_cons_right :
  forall `(r : s ->> t, q : u ->> v, p : v [>] w),
    r <= q ->
    r <= Cons q p.
Proof.
induction r as [t | s t r z o _ | s t f IH]; intros u v q w p H.
constructor.
dependent destruction H.
apply (@Embed_Cons u w (Cons q p) s (inr _ i) r).
assumption.
constructor.
intro n.
apply IH.
dependent destruction H.
trivial.
Qed.

Lemma embed_cons_intro :
  forall `(r : s ->> t, q : u ->> t, p : t [>] v),
    r <= q ->
    Cons r p <= Cons q p.
Proof.
intros.
apply (@Embed_Cons u v (Cons q p) s (inl _ tt) r).
assumption.
Qed.

Lemma embed_lim_right :
  forall `(r : s ->> t, f : (nat -> { v' : term & u ->> v' })) v n,
    r <= (|f n|) ->
    r <= Lim v f.
Proof.
induction r as [t | s t r w p _ | s t f IH]; intros u g v n H.
constructor.
dependent destruction H.
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

Lemma embed_trans :
  forall `(r : s ->> t, q : u ->> v, x : w ->> z),
    r <= q ->
    q <= x ->
    r <= x.
Proof.
intros s t r u v q w z x H1.
revert w z x.
induction H1 as [s u v q | u v q s i r H IH | s f u v q t H IH]; intros w z x H2.
constructor.
induction H2 as [u w z x | w z x u j q H' IH' | u f w z x v H' IH'].
destruct i.
destruct i as [[] | i']; simpl in * |- *.
apply Embed_Cons.
apply IH.
assumption.
apply embed_pref_right with j.
apply IH'.
assumption.
assumption.
destruct i as [n i]; simpl in * |- *.
apply (IH' n i r H IH).
constructor.
intro n.
exact (IH n w z x H2).
Qed.

(*
   This lemma seems very hard to prove directly, but fortunately we can use
   our results on ordinals with the length of sequences.
*)
Lemma embed_not_cons :
  forall `(r : s ->> t, p : t [>] u),
    ~ Cons r p <= r.
Proof.
intros s t r u p H.
assert (H1 := embed_length H).
contradict H1.
apply ord'_le_not_succ.
Qed.

Lemma embed_not_pref_right_strong :
  forall `(r : s ->> t, q : u ->> v, i : pref_type r),
    r <= q ->
    ~ q <= fst (|pref r i|).
Proof.
induction r as [t | s t r w p IH | s t f IH]; intros u v q i H1 H2.
destruct i.
destruct i as [[] | i]; simpl in H2.
apply (embed_not_cons (embed_trans H1 H2)).
exact (IH u v q i (embed_cons_left H1) H2).
destruct i as [n i]; simpl in H2.
dependent destruction H1.
exact (IH n u v q i (H n) H2).
Qed.

Lemma embed_not_pref_right :
  forall `(r : s ->> t, i : pref_type r),
    ~ r <= fst (|pref r i|).
Proof.
intros.
apply embed_not_pref_right_strong.
apply embed_refl.
Qed.

Lemma embed_strict_cons_right :
  forall `(r : s ->> t, q : u ->> v, p : v [>] w),
    r < q ->
    r < Cons q p.
Proof.
intros s t r u v q w p.
destruct 1 as [i H].
exists (inl (pref_type q) tt).
apply embed_pref_right with i.
assumption.
Qed.

Lemma embed_strict_embed :
  forall `(r : s ->> t, q : u ->> v),
    r < q ->
    r <= q.
Proof.
intros s t r u v q.
destruct 1 as [i H].
apply embed_pref_right with i.
assumption.
Qed.

Lemma embed_strict_trans :
  forall `(r : s ->> t, q : u ->> v, x : w ->> z),
    r < q ->
    q < x ->
    r < x.
Proof.
intros s t r u v q w z x.
destruct 1 as [i Hi].
destruct 1 as [j Hj].
exists j.
apply embed_trans with u v q; [apply embed_pref_right with i |]; assumption.
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

(*
   Some kind of weaker variant of weak convergence that we call
   well-formedness for now.
   This does not imply weak convergence because f n and f Sn
   might differ in length more than one step.
   The idea is that, while not implying convergence, wf says
   that at least limits are well-defined.
*)
Fixpoint wf `(r : s ->> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => wf q
  | Lim _ t f      =>
    (forall n, wf (|f n|)) /\
    forall d, exists n, forall m,
      (n <= m)%nat ->
      term_eq_up_to d ($ f m $) t
  end.

(* TODO: with a bit of thinking there might room for generalizing
   good and wf in some way... *)

(*
   Weakly convergent sequences have limit functions f where for
   any depth d, from some n, the end term of r is equal up to
   depth d where (|f n|) <= r and r is contained in the limit.
*)
Fixpoint weakly_convergent `(r : s ->> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => weakly_convergent q
  | Lim _ t f      =>
    (forall n, weakly_convergent (|f n|)) /\
    forall d, exists n, forall j,
      (|f n|) <= fst (|pref r j|) ->
      term_eq_up_to d (fst ($ pref r j $)) t
  end.

Fixpoint strongly_convergent `(r : s ->> t) : Prop :=
  weakly_convergent r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => strongly_convergent q
  | Lim _ t f      =>
    (forall n, strongly_convergent (|f n|)) /\
    forall d, exists i, forall j,
      fst (|pref r i|) <= fst (|pref r j|) ->
      (depth (snd (| pref r j |)) > d)%nat
  end.

(*
   Another idea worth checking: define an order on pref
   indices ('i' is included in 'inr i' etc) and define
   weak convergence using this order instead of <= on the
   sequences.
   This might be closer to what we would do if the indices
   were natural numbers.
*)

(*
   TODO: increasing in strength, should these properties on sequences also
   include the weaker properties?
   Now we always have to state all of them, e.g.

     good r /\ wf r /\ weakly_convergent r /\ strongly_convergent r

   (Note that weak convergence does not imply strong convergence.)
*)

(*
Fixpoint weakly_convergent `(r : s ->> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => weakly_convergent q
  | Lim _ t f      =>
    (forall n, weakly_convergent (|f n|)) /\
    forall d, exists i, forall j,
      fst (|pref r i|) <= fst (|pref r j|) ->
      term_eq_up_to d (fst ($ pref r j $)) t
  end.
*)

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
      (|pref r i|) <= (|pref r j|) ->
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

(* This might be usefull sometimes *)
Fixpoint finite `(r : s ->> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => finite q
  | Lim _ t f      => False
  end.

Lemma good_finite :
  forall `(r : s ->> t),
    finite r ->
    good r.
Proof.
induction r as [t | s t r u p IH | s t f IH]; intro H.
exact I.
apply IH.
assumption.
elim H.
Qed.

Lemma wf_finite :
  forall `(r : s ->> t),
    finite r ->
    wf r.
Proof.
induction r as [t | s t r u p IH | s t f IH]; intro H.
exact I.
apply IH.
assumption.
elim H.
Qed.

Lemma weakly_convergent_finite :
  forall `(r : s ->> t),
    finite r ->
    weakly_convergent r.
Proof.
induction r as [t | s t r u p IH | s t f IH]; intro H.
exact I.
apply IH.
assumption.
elim H.
Qed.

Fixpoint snoc_rec (s t u : term) (r : t ->> u) : s [>] t -> s ->> u :=
  match r in t ->> u return s [>] t -> s ->> u with
  | Nil _          => fun p => Cons (Nil s) p
  | Cons _ _ q _ o => fun p => Cons (snoc_rec q p) o
  | Lim _ u f      => fun p => Lim u (fun o => existT (fun u => s ->> u) ($ f o $) (snoc_rec (| f o|) p))
  end.

Definition snoc `(p : s [>] t, r : t ->> u) : s ->> u := snoc_rec r p.

Lemma pref_snoc :
  forall `(p : s [>] t, r : t ->> u),
    exists i, pref (snoc p r) i = pref (Cons (Nil s) p) (inl _ tt).
Proof.
induction r as [u | t u r v o IH | t u f IH].
exists (inl _ tt); reflexivity.
specialize IH with p.
destruct IH as [i IH].
exists (inr _ i); simpl.
rewrite IH; reflexivity.
specialize IH with 0 p.
destruct IH as [i IH].
exists (existT (fun n => pref_type (snoc p (|f n|))) 0 i); simpl.
rewrite IH; reflexivity.
Qed.

Lemma embed_snoc_right :
  forall `(r : s ->> t, p : u [>] s),
    r <= snoc p r.
Proof.
induction r as [s | s t r v o IH | s t f IH]; intros u p; simpl.
constructor.
apply embed_cons_intro.
apply IH.
constructor.
intro n.
apply embed_lim_right with n.
apply IH.
Qed.

(* This proof is quite hairy and ad-hoc *)
Lemma snoc_embed :
  forall `(p : s [>] t, r : t ->> u, q : t ->> v),
    r <= q ->
    snoc p r <= snoc p q.
Proof.
intros s t p u r v q H.
dependent induction H.
induction q as [t | t v q w o IH | t v f IH]; simpl.
apply embed_refl.
apply embed_cons_right; simpl in IH.
trivial.
apply embed_lim_right with 0; simpl in IH |- *.
trivial.
induction q as [t | t v q w o IH | t v f IH]; simpl.
destruct i.
destruct i as [[] | i].
simpl.
change (Cons (snoc p r) (snd (|pref (Cons (snoc p q) o) (inl _ tt) |)) <= Cons (snoc p q) o).
apply (@Embed_Cons s w (Cons (snoc p q) o) s (inl _ tt) (snoc p r)).
simpl. simpl in IH. simpl in IHembed.
apply IHembed.
assumption.
simpl in H. simpl in IH. simpl in IHembed. fold (@pref_type t v) in i.
apply embed_cons_right.
apply IH.
assumption.
trivial.
destruct i as [n i].
simpl.
apply embed_lim_right with n.
simpl. simpl in IHembed. simpl in H. simpl in r. fold (@pref_type t ($ f n $)) in i.
apply IH.
assumption.
assumption.
simpl.
constructor.
simpl.
intro n.
apply H0.
assumption.
Qed.

Lemma snoc_embed_strict :
  forall `(p : s [>] t, r : t ->> u, q : t ->> v),
    r < q ->
    snoc p r < snoc p q.
Proof.
intros s t p u r v q H.
unfold embed_strict; destruct H as [i H].
induction q as [t | t v q w o _ | t v f IH]; simpl.
destruct i.
exists (inl _ tt); simpl.
apply snoc_embed.
destruct i as [[] | i]; simpl in H.
assumption.
apply embed_pref_right with i.
assumption.
destruct i as [n i]; simpl in H; fold (@pref_type t ($ f n $)) in i.
specialize IH with n p r i.
destruct IH as [j IH].
assumption.
exists (existT (fun n => pref_type (snoc p (|f n|))) n j).
assumption.
Qed.

Lemma embed_not_snoc_nil :
  forall `(p : s [>] t, r : t ->> u) v,
    ~ snoc p r <= Nil v.
Proof.
induction r as [u | t u r w o IH | t u f IH]; simpl; intros v H.
dependent destruction H.
elim i.
dependent destruction H.
elim i.
dependent destruction H.
specialize H with 0.
contradict H.
apply IH.
Qed.

Lemma embed_snoc_elim :
  forall `(p : s [>] t, r : t ->> u, o : v [>] w, q : w ->> z),
    snoc p r <= snoc o q ->
    r <= q.
Proof.
(* TODO: not sure if this can be proved, but it is important! *)
(* Not even sure if it is true... *)
Admitted.

Lemma snoc_finite :
  forall `(p : s [>] t, r : t ->> u),
    finite r ->
    finite (snoc p r).
Proof.
induction r as [u | t u r v o IH | t u f IH]; simpl; intro H.
exact I.
apply IH.
assumption.
elim H.
Qed.

Lemma snoc_good :
  forall `(p : s [>] t, r : t ->> u),
    good r ->
    good (snoc p r).
Proof.
induction r as [u | t u r v o IH | t u f IH]; simpl.
trivial.
apply IH.
intros [H1 H2].
split.
intro n.
apply IH.
apply H1.
intros n m H.
apply snoc_embed_strict.
apply H2.
assumption.
Qed.

Lemma snoc_weakly_convergent_helper :
  forall d x `(p : s [>] t, r : t ->> u, q : t ->> v, j : pref_type (snoc p q)),
    snoc p r <= fst (|pref (snoc p q) j |) ->
    exists i : pref_type q,
      r <= fst (|pref q i|) /\
      (term_eq_up_to d (fst ($ pref q i $)) x ->
        term_eq_up_to d (fst ($ pref (snoc p q) j $)) x).
Proof.
induction q as [v | t v q w o IH | t v f IH]; simpl; intros j H.
destruct j as [[] | []].
contradict H.
apply embed_not_snoc_nil.
destruct j as [[] | j].
simpl in H.
exists (inl _ tt). simpl.
split.
apply embed_snoc_elim with p s p.
assumption.
trivial.
specialize IH with p r j.
destruct IH as [i H1].
assumption.
exists (inr _ i).
assumption.
destruct j as [n j].
specialize IH with n p r j.
destruct IH as [i H1].
assumption.
exists (existT _ n i).
assumption.
Qed.

Lemma snoc_weakly_convergent :
  forall `(p : s [>] t, r : t ->> u),
    weakly_convergent r ->
    weakly_convergent (snoc p r).
Proof.
intros s t p u r H.
induction r.
trivial.
simpl.
apply IHr.
apply H.
split; simpl.
intro n.
apply H0.
apply H.
intro d.
simpl in H.
destruct H as [_ H].
specialize H with d.
destruct H as [n H].
exists n.
intros [m j] H1.
(* this seems a rather strange way of proving *)
destruct (snoc_weakly_convergent_helper d t p (|f n|) (|f m|) j) as [i M].
assumption.
specialize H with (existT (fun n => pref_type (|f n|)) m i).
simpl in H.
apply M.
apply H.
apply M.
Qed.

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
induction q as [u | t u q v p IH | t u f IH]; simpl.
apply ord'_eq_refl.
split.
apply Ord'_le_Succ with (inl (pred_type (add (length r) (length q))) tt).
apply (IH r).
apply Ord'_le_Succ with (inl (pred_type (length (append r q))) tt).
apply (IH r).
split; constructor; intro n; apply ord'_le_limit_right with n; apply (IH n r).
Qed.

Lemma embed_append_right :
  forall `(r : s ->> t, q : t ->> u),
    r <= append r q.
Proof.
induction q as [u | t u q v p IH | t u f IH]; simpl.
apply embed_refl.
apply embed_cons_right.
apply IH.
apply embed_lim_right with 0.
apply IH.
Qed.

(* TODO: So this proof is a verbatim copy of snoc_embed an thus is
   also quite hairy and ad-hoc
   There might be a way to at least not repeat ourselves here... same
   goes for snoc_embed_strict and append_embed_strict by the way *)
Lemma append_embed :
  forall `(r : s ->> t, q : t ->> u, z : t ->> v),
    q <= z ->
    append r q <= append r z.
Proof.
intros s t r u q v z H.
dependent induction H.
induction z as [t | t v z w o IH | t v f IH]; simpl.
apply embed_refl.
apply embed_cons_right; simpl in IH.
trivial.
apply embed_lim_right with 0; simpl in IH |- *.
trivial.
induction z as [t | t v z w o IH | t v f IH]; simpl.
destruct i.
destruct i as [[] | i].
simpl.
change (Cons (append r r0) (snd (|pref (Cons (append r z) o) (inl _ tt) |)) <= Cons (append r z) o).
apply (@Embed_Cons s w (Cons (append r z) o) s (inl _ tt) (append r r0)).
simpl. simpl in IH. simpl in IHembed.
apply IHembed.
assumption.
simpl in H. simpl in IH. simpl in IHembed. fold (@pref_type t v) in i.
apply embed_cons_right.
apply IH.
assumption.
trivial.
destruct i as [n i].
simpl.
apply embed_lim_right with n.
simpl. simpl in IHembed. simpl in H. simpl in r. fold (@pref_type t ($ f n $)) in i.
apply IH.
assumption.
assumption.
simpl.
constructor.
simpl.
intro n.
apply H0.
assumption.
Qed.

Lemma append_embed_strict :
  forall `(r : s ->> t, q : t ->> u, z : t ->> v),
    q < z ->
    append r q < append r z.
Proof.
intros s t r u q v z H.
unfold embed_strict; destruct H as [i H].
induction z as [t | t v z w o _ | t v f IH]; simpl.
destruct i.
exists (inl _ tt); simpl.
apply append_embed.
destruct i as [[] | i]; simpl in H.
assumption.
apply embed_pref_right with i.
assumption.
destruct i as [n i]; simpl in H; fold (@pref_type t ($ f n $)) in i.
specialize IH with n r q i.
destruct IH as [j IH].
assumption.
exists (existT (fun n => pref_type (append r (|f n|))) n j).
assumption.
Qed.

Lemma append_finite :
  forall `(r : s ->> t, q : t ->> u),
    finite r ->
    finite q ->
    finite (append r q).
Proof.
induction q as [u | t u q v p IH | t u f IH]; simpl; intros H1 H2.
assumption.
apply IH; assumption.
elim H2.
Qed.

Lemma append_good :
  forall `(r : s ->> t, q : t ->> u),
    good r ->
    good q ->
    good (append r q).
Proof.
induction q as [u | t u q v p IH | t u f IH]; simpl.
trivial.
apply IH.
intros G [H1 H2].
split.
intro n.
apply IH.
assumption.
apply H1.
intros n m H.
apply append_embed_strict.
apply H2.
assumption.
Qed.

(* can we use this in append_weakly_convergent? *)
Lemma sdfsfsdf :
  forall d x `(r : s ->> t, q : t ->> u) (i : pref_type (append r q)),

  (forall j : pref_type q,
    q <= fst (|pref q j|) ->
    term_eq_up_to d (fst ($ pref q j $)) x) ->

  append r q <= fst (|pref (append r q) i|) ->

  term_eq_up_to d (fst ($ pref (append r q) i $)) x.
Proof.
intros d x s t r u q i H1 H2.
induction q as [u | t u q w p IH | t u f IH].
contradict H2.
apply embed_not_pref_right.
destruct i as [[] | i].
simpl in H2 |- *.
clear H1.
Admitted.


Lemma embed_not_append_pref_left :
  forall `(r : s ->> t, q : t ->> u, j : pref_type r),
    ~ append r q <= fst (|pref r j |).
Proof.
induction q; simpl; intros i H1.
contradict H1.
apply embed_not_pref_right.
dependent destruction H1.
destruct (pref_trans i i0) as [j H].
specialize IHq with r j.
apply IHq.
rewrite H.
assumption.
dependent destruction H1.
specialize H0 with 0.
contradict H0.
apply H.
Qed.

Lemma append_weakly_convergent_helper :
  forall d x `(r : s ->> t, q : t ->> u, y : t ->> v, j : pref_type (append r y)),
    append r q <= fst (|pref (append r y) j |) ->
    exists i : pref_type y,
      q <= fst (|pref y i|) /\
      (term_eq_up_to d (fst ($ pref y i $)) x ->
        term_eq_up_to d (fst ($ pref (append r y) j $)) x).
Proof.
induction y as [v | t v y w o IH | t v f IH]; simpl; intros j H.
contradict H.
apply embed_not_append_pref_left.
destruct j as [[] | j]; simpl in H.
exists (inl _ tt). simpl.
split.
(* TODO: hm this doesn't seem to hold *)

(*
apply append_snoc_elim with p s p.
assumption.
trivial.
specialize IH with p r j.
destruct IH as [i H1].
assumption.
exists (inr _ i).
assumption.
destruct j as [n j].
specialize IH with n p r j.
destruct IH as [i H1].
assumption.
exists (existT _ n i).
assumption.
*)
Admitted.

Lemma append_weakly_convergent :
  forall `(r : s ->> t, q : t ->> u),
    weakly_convergent r ->
    weakly_convergent q ->
    weakly_convergent (append r q).
Proof.
induction q as [u | t u q v p IH | t u f IH]; simpl.
trivial.
apply IH.
intros H1 [H2 H3].
split.
intro n.
apply IH.
assumption.
apply H2.
intro d.
specialize H3 with d.
destruct H3 as [n H3].
exists n.
intros [m j] H.
(* TODO: this depends on the helper lemma, which is probably not correct *)
destruct (append_weakly_convergent_helper d u r (|f n|) (|f m|) j) as [i M].
assumption.
specialize H3 with (existT (fun n => pref_type (|f n|)) m i).
simpl in H3.
apply M.
apply H3.
apply M.
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
