(* Inductive defintion for rewriting sequences *)


Require Import Prelims.
Require Export List.
Require Export FiniteTerm.
Require Export Term.
Require Export Substitution.
Require Export Context.
Require Export Ordinal.
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

(* f converges to t *)
Definition converges (f : nat -> term) (t : term) : Prop :=
  forall d, exists n, forall m,
    (n <= m)%nat ->
    term_eq_up_to d (f m) t.

Reserved Notation "s ->> t" (no associativity, at level 40).

(*
   TODO: shouldn't Cons actually ask for bisimilarity?
   | Cons  : forall `(r : s ->> t, p : u [>] v), t [=] u -> s ->> v
*)
(* We would have defined the Lim with a sig type, but then we end up with a
   non strictly positive occurrence... *)
(*
Inductive sequence : term -> term -> Type :=
  | Nil   : forall t, t ->> t
  | Cons  : forall `(r : s ->> t, p : t [>] u), s ->> u
  | Lim   : forall s t (f : nat -> { t' : term & s ->> t'}), converges (fun n => $ f n $) t -> s ->> t
where "s ->> t" := (sequence s t).
*)
Inductive sequence : term -> term -> Type :=
  | Nil   : forall t, t ->> t
  | Cons  : forall `(r : s ->> t, p : t [>] u), s ->> u
  | Lim   : forall `(f : forall n, s ->> ts n, c : converges ts t), s ->> t
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
  forall `(f : forall n, s ->> ts n, c : converges ts t),
    (forall n, P (f n)) ->
    P (Lim f c).

(* TODO: scope for notations *)
(* TODO: is Lim the best constructor name (compare Limit in ord)? *)
Fixpoint sequence_rect `(r : s ->> t) : P r :=
  match r return P r with
  | Nil t          => H1 t
  | Cons s t r u p => H2 p (sequence_rect r)
  | Lim s ts f t c => H3 f c (fun n => sequence_rect (f n))
  end.

End InductionPrinciple.

Definition sequence_ind (P : `(s ->> t -> Prop)) :=
  sequence_rect P.

Definition cons_term_bis `(r : s ->> t, p : u [>] v) : u [~] t -> s ->> v :=
  match p in u [>] v return u [~] t -> s ->> v with
  | Step u v rul c sub Hr Hs Ht =>
      fun H => Cons r (Step rul c sub Hr (term_bis_trans Hs H) Ht)
  end.

Fixpoint length `(r : s ->> t) : ord :=
  match r with
  | Nil _          => Zero
  | Cons _ _ r _ _ => Succ (length r)
  | Lim _ _ f _ _  => Limit (fun n => length (f n))
  end.

(* TODO: maybe we should delete this unsighty lemma *)
Lemma length_limit_discriminate :
  forall `(r : s ->> t) f,
    length r = Limit f ->
    exists ts : nat -> term, exists g, exists c, r = Lim (ts := ts) g c.
Proof.
intros s t [| | u v g] f H.
discriminate H.
discriminate H.
exists v; exists g; exists c; reflexivity.
Qed.

Fixpoint prd_type `(r : s ->> t) : Type :=
  match r with
  | Nil _          => False
  | Cons _ _ r _ _ => (unit + prd_type r) % type
  | Lim _ _ f _ _  => { n : nat & prd_type (f n) }
  end.

Reserved Notation "r [ i ]" (at level 60).

Fixpoint prd `(r : s ->> t) :
  prd_type r -> { ts : (term * term)%type & ((s ->> (fst ts)) * ((fst ts) [>] (snd ts)))%type } :=
  match r in s ->> t return prd_type r -> { ts : (term * term)%type & ((s ->> (fst ts)) * ((fst ts) [>] (snd ts)))%type } with
  | Nil _           => !
  | Cons s t' q u p => fun i => match i with
                                  (* TODO: i would like t instead of u here *)
                                | inl tt => existT (fun ts => (s ->> fst ts) * (fst ts [>] snd ts))%type (t', u) (q, p)
                                | inr j  => q[j]
                                end
  | Lim _ _ f _ _   => fun i => match i with
                                | existT n j => (f n)[j]
                                end
  end
where "r [ i ]" := (prd r i).

Notation "r [1 i ]" := (fst (projT1 (prd r i))) (at level 60).
Notation "r [2 i ]" := (snd (projT1 (prd r i))) (at level 60).
Notation "r [seq i ]" := (fst (projT2 (prd r i))) (at level 60).
Notation "r [stp i ]" := (snd (projT2 (prd r i))) (at level 60).

Lemma prd_trans :
  forall `(r : s ->> t, i : prd_type r, j : prd_type (r[seq i])),
    exists k : prd_type r, r[k] = r[seq i][j].
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
exists (existT (fun n => prd_type (f n)) n k).
assumption.
Qed.

Implicit Arguments prd_trans [s t r].

(* maybe this could be a coercion *)
Fixpoint prd_type_as_pred_type `(r : s ->> t) : prd_type r -> pred_type (length r) :=
  match r in s ->> t return prd_type r -> pred_type (length r) with
  | Nil _          => !
  | Cons _ _ q _ _ => fun i => match i with
                               | inl tt => inl _ tt
                               | inr j  => inr _ (prd_type_as_pred_type q j)
                               end
  | Lim _ _ f _ _  => fun i => match i with
                               | existT n j => existT _ n (prd_type_as_pred_type (f n) j)
                               end
  end.

Implicit Arguments prd_type_as_pred_type [s t r].

Lemma prd_type_as_pred_type_ok :
  forall `(r : s ->> t, i : prd_type r),
    length (r[seq i]) = pred (length r) (prd_type_as_pred_type i).
Proof.
intros s t r i.
induction r as [t| s t r u p IH | s ts f t c IH].
elim i.
destruct i as [[] | i].
reflexivity.
apply IH.
destruct i as [n i].
apply IH.
Qed.

Fixpoint pred_type_as_prd_type `(r : s ->> t) : pred_type (length r) -> prd_type r :=
  match r in s ->> t return pred_type (length r) -> prd_type r with
  | Nil _          => !
  | Cons _ _ q _ _ => fun i => match i with
                               | inl tt => inl _ tt
                               | inr j  => inr _ (pred_type_as_prd_type q j)
                               end
  | Lim _ _ f _ _  => fun i => match i with
                               | existT n j => existT _ n (pred_type_as_prd_type (f n) j)
                               end
  end.

Implicit Arguments pred_type_as_prd_type [s t r].

Lemma pred_type_as_prd_type_ok :
  forall `(r : s ->> t, i : pred_type (length r)),
    length (r[seq pred_type_as_prd_type i]) = ((length r)[i])%ord.
Proof.
intros s t r i.
induction r as [t| s t r u p IH | s ts f t c IH].
elim i.
destruct i as [[] | i]; simpl.
reflexivity.
apply IH.
destruct i as [n i]; simpl.
apply IH.
Qed.

Lemma pred_type_prd_type_inv :
  forall `(r : s ->> t, i : prd_type r),
    i = pred_type_as_prd_type (prd_type_as_pred_type i).
Proof.
intros s t r i.
induction r as [t| s t r u p IH | s ts f t c IH].
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
  | Embed_Cons : forall `(q : u ->> v, r : s ->> (q[1 i])),
                   r <= q[seq i] ->
                   Cons r (q[stp i]) <= q
  | Embed_Lim  : forall `(f : (forall n, s ->> ts n), c : converges ts t, q : u ->> v),
                   (forall n, (f n) <= q) ->
                   Lim f c <= q
where "r <= q" := (embed r q).

Definition embed_strict `(r : s ->> t, q : u ->> v) := exists i, r <= q[seq i].
Infix " < " := embed_strict (no associativity, at level 70).

Lemma embed_length :
  forall `(r : s ->> t, q : u ->> v),
    r <= q -> (length r <= length q)%ord.
Proof.
induction r as [t | s t r w p IH | s ts f t c IH]; simpl; intros u v q H.
constructor.
dependent destruction H.
apply Ord_le_Succ with (prd_type_as_pred_type i).
rewrite <- prd_type_as_pred_type_ok.
apply IH.
assumption.
dependent destruction H.
constructor.
intro n.
apply IH.
apply H.
Qed.

Lemma embed_prd_right :
  forall `(r : s ->> t, q : u ->> v, i : prd_type q),
    r <= q[seq i] ->
    r <= q.
Proof.
induction r as [t | s t r w p IH | s ts f t c IH]; intros u v q i H.
constructor.
dependent destruction H.
destruct (prd_trans i i0) as [k T].
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

Lemma embed_prd_left :
  forall `(r : s ->> t, q : u ->> v, i : prd_type r),
    r <= q ->
    r[seq i] <= q.
Proof.
intros s t r u v q i H.
induction H as [s u v q | u v q s j r H IH | s ts f t c u v q H IH].
elim i.
destruct i as [[] | i]; apply embed_prd_right with j.
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
destruct i as [[] |]; [| apply embed_prd_right with p]; assumption.
Qed.

Lemma first_prd_after_cons_id :
  forall `(r : s ->> t, p : t [>] u),
    r = (Cons r p)[seq (inl (prd_type r) tt)].
Proof.
trivial.
Qed.

Lemma embed_cons_left :
  forall `(r : s ->> t, q : v ->> w, p : t [>] u),
    Cons r p <= q ->
    r <= q.
Proof.
intros s t r v w q u p H.
rewrite (first_prd_after_cons_id r) with p.
apply (@embed_prd_left s u (Cons r p) v w q (inl (prd_type r) tt)).
assumption.
Qed.

Lemma embed_cons_right :
  forall `(r : s ->> t, q : u ->> v, p : v [>] w),
    r <= q ->
    r <= Cons q p.
Proof.
induction r as [t | s t r z o _ | s ts f t c IH]; intros u v q w p H.
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
  forall `(r : s ->> t, f : (forall n, u ->> ts n), c : converges ts v) n,
    r <= f n ->
    r <= Lim f c.
Proof.
induction r as [t | s t r w p _ | s ts f t c IH]; intros u ts' g v c' n H.
constructor.
dependent destruction H.
apply (@Embed_Cons u v (Lim g c') s (existT (fun n => prd_type (g n)) n i) r).
assumption.
constructor.
intro m.
apply (IH m u ts' g v c' n).
dependent destruction H.
trivial.
Qed.

Lemma embed_refl :
  forall `(r : s ->> t), r <= r.
Proof.
induction r as [t | s t r u p IH | s ts f t c IH].
constructor.
apply Embed_Cons with (q := Cons r p) (i := inl (prd_type r) tt).
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
induction H1 as [s u v q | u v q s i r H IH | s ts f t c u v q H IH]; intros w z x H2.
constructor.
induction H2 as [u w z x | w z x u j q H' IH' | u ts' f v c' w z x H' IH'].
destruct i.
destruct i as [[] | i']; simpl in * |- *.
apply Embed_Cons.
apply IH.
assumption.
apply embed_prd_right with j.
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
apply ord_le_not_succ.
Qed.

Lemma embed_not_prd_right_strong :
  forall `(r : s ->> t, q : u ->> v, i : prd_type r),
    r <= q ->
    ~ q <= r[seq i].
Proof.
induction r as [t | s t r w p IH | s ts f t c IH]; intros u v q i H1 H2.
destruct i.
destruct i as [[] | i]; simpl in H2.
apply (embed_not_cons (embed_trans H1 H2)).
exact (IH u v q i (embed_cons_left H1) H2).
destruct i as [n i]; simpl in H2.
dependent destruction H1.
exact (IH n u v q i (H n) H2).
Qed.

Lemma embed_not_prd_right :
  forall `(r : s ->> t, i : prd_type r),
    ~ r <= r[seq i].
Proof.
intros.
apply embed_not_prd_right_strong.
apply embed_refl.
Qed.

Lemma embed_strict_cons_right :
  forall `(r : s ->> t, q : u ->> v, p : v [>] w),
    r < q ->
    r < Cons q p.
Proof.
intros s t r u v q w p.
destruct 1 as [i H].
exists (inl (prd_type q) tt).
apply embed_prd_right with i.
assumption.
Qed.

Lemma embed_strict_embed :
  forall `(r : s ->> t, q : u ->> v),
    r < q ->
    r <= q.
Proof.
intros s t r u v q.
destruct 1 as [i H].
apply embed_prd_right with i.
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
apply embed_trans with u v q; [apply embed_prd_right with i |]; assumption.
Qed.

(* TODO: move to Ordinal *)
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
  | Lim _ _ f t _  =>
    (forall n, good (f n)) /\
    forall n m, (n < m)%nat -> f n < f m
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
  | Lim _ ts f t _ =>
    (forall n, wf (f n)) /\
    forall d, exists n, forall m,
      (n <= m)%nat ->
      term_eq_up_to d (ts m) t
  end.

(* TODO: This proofs wf is no longer needed *)
Lemma wf_dumb : forall `(r : s ->> t), wf r.
Proof.
induction r as [t | s t r w p IH | s ts f t c IH].
exact I.
exact IH.
split.
exact IH.
exact c.
Qed.

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
  | Lim _ _ f t _  =>
    (forall n, weakly_convergent (f n)) /\
    forall d, exists n, forall j,
      f n <= r[seq j] ->
      term_eq_up_to d (r[1 j]) t
  end.

Fixpoint strongly_convergent `(r : s ->> t) : Prop :=
  weakly_convergent r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => strongly_convergent q
  | Lim _ _ f t _  =>
    (forall n, strongly_convergent (f n)) /\
    forall d, exists i, forall j,
      r[seq i] <= r[seq j] ->
      (depth (r[stp j]) > d)%nat
  end.

Fixpoint all_terms_eq_up_to d `(r : s ->> t) u : Prop :=
  match r with
  | Nil s          => term_eq_up_to d s u
  | Cons _ _ q t _ => all_terms_eq_up_to d q u /\ term_eq_up_to d t u
  | Lim _ _ f t _  =>
    (forall n, all_terms_eq_up_to d (f n) u) /\ term_eq_up_to d t u
  end.

Lemma all_terms_eq_up_to_0 :
  forall `(r : s ->> t, u : term),
    all_terms_eq_up_to 0 r u.
Proof.
induction r as [t | s t r v p IH | s ts f t c IH]; simpl; intro q.
constructor.
split.
apply IH.
constructor.
split.
intro n; apply IH.
constructor.
Qed.

(*
   Another idea worth checking: define an order on prd
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
      fst (|prd r i|) <= fst (|prd r j|) ->
      term_eq_up_to d (fst ($ prd r j $)) t
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
   of all prdixes of such an (f m) having at leas length (f n) should be
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
      (|prd r i|) <= (|prd r j|) ->
      term_eq_up_to d ($ prd r j $) t
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
      (|prd r i|) <= (|prd r j|) ->
      step_below d (|prd r j|)
  end.
*)

(* TODO: maybe it's cleaner to define this via ordinal length *)
Fixpoint finite `(r : s ->> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => finite q
  | Lim _ _ f t c  => False
  end.

Lemma good_finite :
  forall `(r : s ->> t),
    finite r ->
    good r.
Proof.
induction r as [t | s t r u p IH | s ts f t c IH]; intro H.
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
induction r as [t | s t r u p IH | s ts f t c IH]; intro H.
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
induction r as [t | s t r u p IH | s ts f t c IH]; intro H.
exact I.
apply IH.
assumption.
elim H.
Qed.

Fixpoint snoc_rec (s t u : term) (r : t ->> u) : s [>] t -> s ->> u :=
  match r in t ->> u return s [>] t -> s ->> u with
  | Nil _          => fun p => Cons (Nil s) p
  | Cons _ _ q _ o => fun p => Cons (snoc_rec q p) o
  | Lim _ _ f u c  => fun p => Lim (fun o => snoc_rec (f o) p) c
  end.

Definition snoc `(p : s [>] t, r : t ->> u) : s ->> u := snoc_rec r p.

Lemma all_terms_eq_up_to_snoc :
  forall d `(p : s [>] t, r : t ->> u, v : term),
    term_eq_up_to d s v ->
    all_terms_eq_up_to d r v ->
    all_terms_eq_up_to d (snoc p r) v.
Proof.
induction r as [u | t u r w o IH | t us f u c IH]; simpl; intros v Hs Hr.
split; assumption.
split.
apply IH.
assumption.
apply Hr.
apply Hr.
split.
intro n.
apply IH.
assumption.
apply Hr.
apply Hr.
Qed.

(* TODO: i don't think this is a meaningfull lemma *)
Lemma prd_snoc :
  forall `(p : s [>] t, r : t ->> u),
    exists i, (snoc p r)[i] = Cons (Nil s) p [(inl _ tt)].
Proof.
induction r as [u | t u r v o IH | t us f u c IH].
exists (inl _ tt); reflexivity.
specialize IH with p.
destruct IH as [i IH].
exists (inr _ i); simpl.
rewrite IH; reflexivity.
specialize IH with 0 p.
destruct IH as [i IH].
exists (existT (fun n => prd_type (snoc p (f n))) 0 i); simpl.
rewrite IH; reflexivity.
Qed.

Lemma embed_snoc_right :
  forall `(r : s ->> t, p : u [>] s),
    r <= snoc p r.
Proof.
induction r as [s | s t r v o IH | s ts f t c IH]; intros u p; simpl.
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
induction q as [t | t v q w o IH | t vs f v c IH]; simpl.
apply embed_refl.
apply embed_cons_right; simpl in IH.
trivial.
apply embed_lim_right with 0; simpl in IH |- *.
trivial.
induction q as [t | t v q w o IH | t vs f v c IH]; simpl.
destruct i.
destruct i as [[] | i].
simpl.
change (Cons (snoc p r) (Cons (snoc p q) o [stp inl _ tt]) <= Cons (snoc p q) o).
apply (@Embed_Cons s w (Cons (snoc p q) o) s (inl _ tt) (snoc p r)).
simpl. simpl in IH. simpl in IHembed.
apply IHembed.
assumption.
simpl in H. simpl in IH. simpl in IHembed. fold (@prd_type t v) in i.
apply embed_cons_right.
apply IH.
assumption.
trivial.
destruct i as [n i].
simpl.
apply embed_lim_right with n.
simpl. simpl in IHembed. simpl in H. simpl in r. fold (prd_type (f n)) in i.
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
induction q as [t | t v q w o _ | t vs f v c IH]; simpl.
destruct i.
exists (inl _ tt); simpl.
apply snoc_embed.
destruct i as [[] | i]; simpl in H.
assumption.
apply embed_prd_right with i.
assumption.
destruct i as [n i]; simpl in H; fold (prd_type (f n)) in i.
specialize IH with n p r i.
destruct IH as [j IH].
assumption.
exists (existT (fun n => prd_type (snoc p (f n))) n j).
assumption.
Qed.

Lemma embed_not_snoc_nil :
  forall `(p : s [>] t, r : t ->> u) v,
    ~ snoc p r <= Nil v.
Proof.
induction r as [u | t u r w o IH | t us f u c IH]; simpl; intros v H.
dependent destruction H.
elim i.
dependent destruction H.
elim i.
dependent destruction H.
specialize H with 0.
contradict H.
apply IH.
Qed.

Lemma embed_snoc_elim_strong :
  forall `(p : s [>] t, r : t ->> u, o : v [>] w, q : w ->> z),
    snoc p r <= snoc o q ->
    r <= q.
Proof.
(* TODO: not sure if this can be proved, not even sure if it is true... *)
Admitted.

(* TODO: tidy *)
Lemma embed_snoc_elim :
  forall `(p : s [>] t, r : t ->> u, q : t ->> v),
    snoc p r <= snoc p q ->
    r <= q.
Proof.
induction r as [u | t u r w o IH | t us f u c IH]; simpl; intros v q H.
constructor.
dependent destruction H.
induction q.
destruct i as [[] | []].
contradict H.
apply embed_not_snoc_nil.
destruct i as [[] | i]; simpl in * |- *.
apply embed_cons_intro.
apply IH with p.
assumption.
fold snoc_rec in i.
apply embed_cons_right.
apply IHq.
assumption.
assumption.
destruct i as [n i].
apply embed_lim_right with n.
simpl.
apply H0.
assumption.
assumption.
constructor.
intro n.
apply IH with p.
dependent destruction H.
apply H.
Qed.

Lemma snoc_finite :
  forall `(p : s [>] t, r : t ->> u),
    finite r ->
    finite (snoc p r).
Proof.
induction r as [u | t u r v o IH | t us f u c IH]; simpl; intro H.
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
induction r as [u | t u r v o IH | t us f u c IH]; simpl.
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
  forall d x `(p : s [>] t, r : t ->> u, q : t ->> v, j : prd_type (snoc p q)),
    snoc p r <= snoc p q [seq j] ->
    exists i : prd_type q,
      r <= q[seq i] /\
      (term_eq_up_to d (q[1 i]) x ->
        term_eq_up_to d (snoc p q [1 j]) x).
Proof.
induction q as [v | t v q w o IH | t vs f v c IH]; simpl; intros j H.
destruct j as [[] | []].
contradict H.
apply embed_not_snoc_nil.
destruct j as [[] | j].
simpl in H.
exists (inl _ tt). simpl.
split.
apply embed_snoc_elim with p.
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
destruct (snoc_weakly_convergent_helper d t p (f n) (f m) j) as [i M].
assumption.
specialize H with (existT (fun n => prd_type (f n)) m i).
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
  | Lim _ _ f u c  => fun r => Lim (fun o => append_rec (f o) r) c
  end.

Definition append `(r : s ->> t, q : t ->> u) : s ->> u := append_rec q r.

Lemma append_length :
  forall `(r : s ->> t, q : t ->> u),
    (length (append r q) == add (length r) (length q)) % ord.
Proof.
induction q as [u | t u q v p IH | t us f u c IH]; simpl.
apply ord_eq_refl.
split.
apply Ord_le_Succ with (inl (pred_type (add (length r) (length q))) tt).
apply (IH r).
apply Ord_le_Succ with (inl (pred_type (length (append r q))) tt).
apply (IH r).
split; constructor; intro n; apply ord_le_limit_right with n; apply (IH n r).
Qed.

Lemma embed_append_right :
  forall `(r : s ->> t, q : t ->> u),
    r <= append r q.
Proof.
induction q as [u | t u q v p IH | t us f u c IH]; simpl.
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
induction z as [t | t v z w o IH | t vs f v c IH]; simpl.
apply embed_refl.
apply embed_cons_right; simpl in IH.
trivial.
apply embed_lim_right with 0; simpl in IH |- *.
trivial.
induction z as [t | t v z w o IH | t vs f v c IH]; simpl.
destruct i.
destruct i as [[] | i].
simpl.
change (Cons (append r r0) (Cons (append r z) o [stp inl _ tt]) <= Cons (append r z) o).
apply (@Embed_Cons s w (Cons (append r z) o) s (inl _ tt) (append r r0)).
simpl. simpl in IH. simpl in IHembed.
apply IHembed.
assumption.
simpl in H. simpl in IH. simpl in IHembed. fold (@prd_type t v) in i.
apply embed_cons_right.
apply IH.
assumption.
trivial.
destruct i as [n i].
simpl.
apply embed_lim_right with n.
simpl. simpl in IHembed. simpl in H. simpl in r. fold (prd_type (f n)) in i.
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
induction z as [t | t v z w o _ | t vs f v c IH]; simpl.
destruct i.
exists (inl _ tt); simpl.
apply append_embed.
destruct i as [[] | i]; simpl in H.
assumption.
apply embed_prd_right with i.
assumption.
destruct i as [n i]; simpl in H; fold (prd_type (f n)) in i.
specialize IH with n r q i.
destruct IH as [j IH].
assumption.
exists (existT (fun n => prd_type (append r (f n))) n j).
assumption.
Qed.

Lemma append_finite :
  forall `(r : s ->> t, q : t ->> u),
    finite r ->
    finite q ->
    finite (append r q).
Proof.
induction q as [u | t u q v p IH | t us f u c IH]; simpl; intros H1 H2.
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
induction q as [u | t u q v p IH | t us f u c IH]; simpl.
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

Lemma prd_append :
  forall `(r : s ->> t, q : t ->> u, i : prd_type r),
    exists j : prd_type (append r q),
      append r q [j] = r[i].
Proof.
induction q as [u | t u q v p IH | t us f u c IH]; simpl; intro i.
exists i.
reflexivity.
destruct (IH r i) as [j H].
exists (inr _ j).
assumption.
destruct (IH 0 r i) as [j H].
exists (existT (fun n => prd_type (append r (f n))) 0 j).
assumption.
Qed.

(* can we use this in append_weakly_convergent? *)
Lemma sdfsfsdf :
  forall d x `(r : s ->> t, q : t ->> u) (i : prd_type (append r q)),

  (forall j : prd_type q,
    q <= q[seq j] ->
    term_eq_up_to d (q[1 j]) x) ->

  append r q <= (append r q)[seq i] ->

  term_eq_up_to d ((append r q)[1 i]) x.
Proof.
intros d x s t r u q i H1 H2.
induction q as [u | t u q w p IH | t us f u c IH].
contradict H2.
apply embed_not_prd_right.
destruct i as [[] | i].
simpl in H2 |- *.
clear H1.
Admitted.


Lemma embed_not_append_prd_left :
  forall `(r : s ->> t, q : t ->> u, j : prd_type r),
    ~ append r q <= r[seq j].
Proof.
induction q; simpl; intros i H1.
contradict H1.
apply embed_not_prd_right.
dependent destruction H1.
destruct (prd_trans i i0) as [j H].
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
  forall d x `(r : s ->> t, q : t ->> u, y : t ->> v, j : prd_type (append r y)),
    append r q <= (append r y)[seq j] ->
    exists i : prd_type y,
      q <= y[seq i] /\
      (term_eq_up_to d (y[1 i]) x ->
        term_eq_up_to d ((append r y)[1 j]) x).
Proof.
induction y as [v | t v y w o IH | t vs f v c IH]; simpl; intros j H.
contradict H.
apply embed_not_append_prd_left.
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
induction q as [u | t u q v p IH | t us f u c IH]; simpl.
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
destruct (append_weakly_convergent_helper d u r (f n) (f m) j) as [i M].
assumption.
specialize H3 with (existT (fun n => prd_type (f n)) m i).
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
      (length r' <= omega)%ord.
Proof.
intros LL s t r SC.
induction r as [t | s t r u p IH | s ts f t c IH].

(* Case (Nil t) *)
exists (Nil t).
split.
trivial.
apply Ord_le_Zero.

(* Case (Cons r p) *)
assert (IH' := (IH (proj2 SC))); clear r SC IH.
destruct IH' as [r [SC IH]].
destruct (ord_le_omega_elim IH) as [[i H] | H]; clear IH.
exists (Cons r p).
split.
admit. (* apply SCr'. *)
apply Ord_le_Succ with i.
assumption.
admit.

(* Case (Lim t f) *)
admit.
Qed.

End TRS.


Implicit Arguments normal_form [F X system].
