(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines the type [s ->> t] of transfinite rewrite
   sequences.

   The inductive definition of rewrite sequences is based on that of the
   tree ordinals (see the [Ordinal] library). A rewrite sequence of ordinal
   length alpha is represented by the tree structure of (the tree ordinal)
   alpha where all [Succ] constructors are labeled with rewrite steps.

   The notion of predecessor index and the order on [ord] are lifted to
   [sequence]. The order then becomes an embedding relation on rewrite
   sequences.

   The lifting of ordinal addition yields a concatenation function on
   rewrite sequences.

   For more information, see:

     Martijn Vermaat.
     Infinitary Rewriting in Coq.
     Master Thesis, VU University Amsterdam, 2010.

   % http://martijn.vermaat.name/master-project %
   # <a href="http://martijn.vermaat.name/master-project">http://martijn.vermaat.name/master-project</a> #
*)


Require Import Prelims.
Require Export List.
Require Export FiniteTerm.
Require Export Term.
Require Export Substitution.
Require Export Context.
Require Export ContextEquality.
Require Export Ordinal.
Require Export TermEquality.
Require Import Equality.


Set Implicit Arguments.


Section Rule.

(** We define rewrite rules as pairs of finite terms with the usual
   restrictions. A term rewriting system (TRS) is a list of rewrite
   rules (where the order of no importance). *)

Variable F : signature.
Variable X : variables.

Notation fterm := (finite_term F X).

(** Rewrite rules of finite terms. *)
Record rule : Type := Rule {
  lhs     : fterm;
  rhs     : fterm;
  rule_wf : is_var lhs = false /\ incl (vars rhs) (vars lhs)
}.

(** Left hand side is linear. *)
Definition left_linear (r : rule) : Prop :=
  linear (lhs r).

(** A Term Rewriting System as a finite list of of rewrite rules. *)
Definition trs := list rule.

(** All rules are left-linear. *)
Definition trs_left_linear (s : trs) : Prop := Forall left_linear s.

End Rule.


Implicit Arguments rule [F X].


Section TRS.

(** We consider a TRS and define rewrite steps over its rewrite rules.
   The rewrite steps are then used to construct transfinite rewrite
   sequences. *)

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

(** Critical pairs denote overlap of rewrite rules. Note that we do not
   consider most general common instances, minimality of substitutions, and
   freshness conditions in the defition of [critical_pair]. This definition
   suffices for our present purposes and is not too complex. *)

(* finite_subterm is a quick hack, substitute should be generalized *)
Definition critical_pair (t1 t2 : term) : Prop :=
  exists r1 : rule, exists r2 : rule,
    exists p : position,
      exists sigma : substitution, exists tau : substitution,
      In r1 system /\ In r2 system /\
      (r1 = r2 -> p <> nil) /\
      match finite_subterm (lhs r1) p, dig (substitute sigma (lhs r1)) p with
      | Some s, Some c =>
          is_var s = false /\
          substitute sigma s [~] substitute tau (lhs r2) /\
          t1 [~] fill c (substitute tau (rhs r2)) /\
          t2 [~] substitute sigma (rhs r1)
      | _, _           => False
      end.

(** An orthogonal TRS is left-linear and has no critical pairs. A weakly
   orthogonal TRS is left-linear and has only trivial critical pairs. *)

Definition orthogonal : Prop :=
  trs_left_linear system /\
  forall t1 t2, ~ critical_pair t1 t2.

Definition weakly_orthogonal : Prop :=
  trs_left_linear system /\
  forall t1 t2, critical_pair t1 t2 -> t1 [~] t2.

(** The type [s [>] t] of rewrite steps is parameterised by source and
   target terms [s] and [t]. We allow some flexivility in [s] and [t] in
   the form of bisimilarity. *)

Reserved Notation "s [>] t" (no associativity, at level 40).

Inductive step : term -> term -> Type :=
  | Step : forall (s t : term) (r : rule) (c : context) (u : substitution),
             In r system ->
             fill c (substitute u (lhs r)) [~] s ->
             fill c (substitute u (rhs r)) [~] t ->
             s [>] t
where "s [>] t" := (step s t).

(** Equality of steps [step_eq] requires;
   - bisimilarity of contexts
   - equality of rules
   - equality of substitutions for all variables in the rule.

   This implies bisimilarity of source and target terms. *)

Definition step_eq `(p : s [>] t, o : u [>] v) :=
  match p, o with
  | Step _ _ r c u _ _ _, Step _ _ r' c' u' _ _ _ =>
    context_bis c c' /\ r = r' /\ substitution_eq (vars (lhs r)) u u'
  end.

(** Note that this lemma is tainted by [substitution_eq_substitute], which
   is not proved yet. See the [Substitution] library. *)
Lemma step_eq_source :
  forall `(p : s [>] t, o : u [>] v),
    step_eq p o ->
    s [~] u.
Proof.
intros _ _ [s t r c a Hr Hs Ht] _ _ [u v r' c' b Hr' Hu Hv] H.
apply term_bis_trans with (fill c (substitute a (lhs r))).
apply term_bis_symm; assumption.
apply term_bis_trans with (fill c' (substitute b (lhs r'))).
destruct H as [H1 [H2 H3]].
rewrite <- H2.
apply term_bis_trans with (fill c (substitute b (lhs r))).
apply fill_term_bis.
apply substitution_eq_substitute.
assumption.
apply fill_context_bis.
assumption.
assumption.
Qed.

(** Note that this lemma is tainted by [substitution_eq_substitute] and
   [substitution_eq_incl, which are not proved yet. See the [Substitution]
   library. *)
Lemma step_eq_target :
  forall `(p : s [>] t, o : u [>] v),
    step_eq p o ->
    t [~] v.
Proof.
intros _ _ [s t r c a Hr Hs Ht] _ _ [u v r' c' b Hr' Hu Hv] H.
apply term_bis_trans with (fill c (substitute a (rhs r))).
apply term_bis_symm; assumption.
apply term_bis_trans with (fill c' (substitute b (rhs r'))).
destruct H as [H1 [H2 H3]].
rewrite <- H2.
apply term_bis_trans with (fill c (substitute b (rhs r))).
apply fill_term_bis.
apply substitution_eq_substitute.
apply substitution_eq_incl with (vars (lhs r)).
apply rule_wf.
assumption.
apply fill_context_bis.
assumption.
assumption.
Qed.

(** [step_eq_refl] is an equivalence. *)

Lemma step_eq_refl :
  forall `(p : s [>] t), step_eq p p.
Proof.
intros _ _ [].
constructor.
apply context_bis_refl.
split.
reflexivity.
apply substitution_eq_refl.
Qed.

Lemma step_eq_symm :
  forall `(p : s [>] t, o : u [>] v),
    step_eq p o ->
    step_eq o p.
Proof.
intros.
destruct p, o.
constructor.
apply context_bis_symm.
apply H.
destruct H as [_ [H H']].
split.
rewrite H.
reflexivity.
apply substitution_eq_symm.
rewrite <- H.
assumption.
Qed.

Lemma step_eq_trans :
  forall `(p : s [>] t, o : u [>] v, m : w [>] z),
    step_eq p o ->
    step_eq o m ->
    step_eq p m.
Proof.
intros.
destruct p, o, m.
constructor.
apply context_bis_trans with c0.
apply H.
apply H0.
destruct H as [_ [H H']].
split.
rewrite H.
apply H0.
apply substitution_eq_trans with u.
apply H'.
rewrite H.
apply H0.
Qed.

(** Depth of rule application in a rewriting step. *)
Definition depth s t (p : s [>] t) : nat :=
  match p with
  | Step _ _ _ c _ _ _ _ => hole_depth c
  end.

(** Source and target terms are equal up to the depth of the rewrite step. *)
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

(** A term is a normal form if no rule left-hand side matches. *)
Definition normal_form t :=
  ~ exists c : context, exists r, exists u,
    In r system /\ fill c (substitute u (lhs r)) [~] t.

(** An alternative formulation would be [~exists p : t [>] _, True]. *)

(** The type [s ->> t] of rewrite sequences is parameterised by source and
   target terms [s] and [t]. This structure is based on that of the tree
   ordinals (see the [Ordinal] library). *)

Reserved Notation "s ->> t" (no associativity, at level 40).

Inductive sequence : term -> term -> Type :=
  | Nil   : forall t, t ->> t
  | Cons  : forall `(r : s ->> t, p : t [>] u), s ->> u
  | Lim   : forall `(f : (forall n, s ->> ts n), c : converges ts t), s ->> t
where "s ->> t" := (sequence s t).

(** Coq ignores the recursive call in the [Lim] constructor and therefore
   the induction principle is missing a hypothesis. We reset the
   generated induction principle and create a new one below.

   UPDATE: This was only true for our old [Sigma] type definition, Coq
   generates a perfectly fine induction principle now. For the moment, we
   keep our own induction principle though, because the order of parameters
   is different (this affects all proofs with [induction r as [...]]). *)

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

Fixpoint sequence_rect `(r : s ->> t) : P r :=
  match r return P r with
  | Nil t          => H1 t
  | Cons s t r u p => H2 p (sequence_rect r)
  | Lim s ts f t c => H3 f c (fun n => sequence_rect (f n))
  end.

End InductionPrinciple.

Definition sequence_ind (P : `(s ->> t -> Prop)) :=
  sequence_rect P.

(** We can [Cons] steps that fit by bisimilarity. *)
Definition cons_term_bis `(r : s ->> t, p : u [>] v) : u [~] t -> s ->> v :=
  match p in u [>] v return u [~] t -> s ->> v with
  | Step u v rul c sub Hr Hs Ht =>
      fun H => Cons r (Step rul c sub Hr (term_bis_trans Hs H) Ht)
  end.

(** Trivial image of rewrite sequences in ordinals. *)
Fixpoint length `(r : s ->> t) : ord :=
  match r with
  | Nil _          => Zero
  | Cons _ _ r _ _ => Succ (length r)
  | Lim _ _ f _ _  => Limit (fun n => length (f n))
  end.

(** We lift [pd_type], [pd], and [ord_le] from ordinals to rewrite sequences.
   See the [Ordinal] library for the original definitions. *)

Fixpoint pred_type `(r : s ->> t) : Type :=
  match r with
  | Nil _          => False
  | Cons _ _ r _ _ => (unit + pred_type r) % type
  | Lim _ _ f _ _  => { n : nat & pred_type (f n) }
  end.

Reserved Notation "r [ i ]" (at level 60).

(** The difference with ordinals is that [Succ] constructors carry no
   additional information, whereas [Cons] constructors carry a rewrite
   step. The predecessor indices of a rewrite sequence always point to
   a [Cons] constructor and it is useful to get both the predecessor
   rewrite sequence and the rewrite step pointed to by the predecessor
   index. Therefore, [pred] returns a pair (rewrite sequence, rewrite
   step). The pair is wrapped in a [Sigma] type that includes the
   source and target terms of the rewrite step. *)
Fixpoint pred `(r : s ->> t) :
  pred_type r -> { ts : (term * term)%type & ((s ->> (fst ts)) * ((fst ts) [>] (snd ts)))%type } :=
  match r in s ->> t return pred_type r -> { ts : (term * term)%type & ((s ->> (fst ts)) * ((fst ts) [>] (snd ts)))%type } with
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
where "r [ i ]" := (pred r i).

Notation "r [1 i ]" := (fst (projT1 (pred r i))) (at level 60).
Notation "r [2 i ]" := (snd (projT1 (pred r i))) (at level 60).
Notation "r [seq i ]" := (fst (projT2 (pred r i))) (at level 60).
Notation "r [stp i ]" := (snd (projT2 (pred r i))) (at level 60).

(** [pred_type] is transitively closed. *)
Lemma pred_trans :
  forall `(r : s ->> t, i : pred_type r, j : pred_type (r[seq i])),
    exists k : pred_type r, r[k] = r[seq i][j].
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
exists (existT (fun n => pred_type (f n)) n k).
assumption.
Qed.

Implicit Arguments pred_trans [s t r].

(** Image of [pred_type] (on rewrite sequences) in [pd_type] (on ordinals).
   Maybe we should make this a coercion. *)

Fixpoint pred_type_as_pd_type `(r : s ->> t) : pred_type r -> pd_type (length r) :=
  match r in s ->> t return pred_type r -> pd_type (length r) with
  | Nil _          => !
  | Cons _ _ q _ _ => fun i => match i with
                               | inl tt => inl _ tt
                               | inr j  => inr _ (pred_type_as_pd_type q j)
                               end
  | Lim _ _ f _ _  => fun i => match i with
                               | existT n j => existT _ n (pred_type_as_pd_type (f n) j)
                               end
  end.

Implicit Arguments pred_type_as_pd_type [s t r].

Lemma pred_type_as_pd_type_ok :
  forall `(r : s ->> t, i : pred_type r),
    length (r[seq i]) = pd (length r) (pred_type_as_pd_type i).
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

(** Image of [pd_type] (on ordinals) in [pred_type] (on rewrite sequences).
   Maybe we should make this a coercion. *)

Fixpoint pd_type_as_pred_type `(r : s ->> t) : pd_type (length r) -> pred_type r :=
  match r in s ->> t return pd_type (length r) -> pred_type r with
  | Nil _          => !
  | Cons _ _ q _ _ => fun i => match i with
                               | inl tt => inl _ tt
                               | inr j  => inr _ (pd_type_as_pred_type q j)
                               end
  | Lim _ _ f _ _  => fun i => match i with
                               | existT n j => existT _ n (pd_type_as_pred_type (f n) j)
                               end
  end.

Implicit Arguments pd_type_as_pred_type [s t r].

Lemma pd_type_as_pred_type_ok :
  forall `(r : s ->> t, i : pd_type (length r)),
    length (r[seq pd_type_as_pred_type i]) = ((length r)[i])%ord.
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

Lemma pd_type_pred_type_inv :
  forall `(r : s ->> t, i : pred_type r),
    i = pd_type_as_pred_type (pred_type_as_pd_type i).
Proof.
intros s t r i.
induction r as [t| s t r u p IH | s ts f t c IH].
elim i.
destruct i as [[] | i]; simpl; [| rewrite <- (IH i)]; reflexivity.
destruct i as [n i]; simpl.
rewrite <- (IH n i).
reflexivity.
Qed.

(** The order [ord_le] on ordinals lifted to rewrite sequences is an embedding
   relation on rewrite sequences. *)

Inductive embed : forall `(r : s ->> t, q : u ->> v), Prop :=
  | Embed_Nil  : forall s `(q : u ->> v),
                   Nil s <= q
  | Embed_Cons : forall `(q : u ->> v, r : s ->> (q[1 i]), p : (q[1 i]) [>] t),
                   r <= q[seq i] ->
                   step_eq p (q[stp i]) ->
                   Cons r p <= q
  | Embed_Lim  : forall `(f : (forall n, s ->> ts n), c : converges ts t, q : u ->> v),
                   (forall n, (f n) <= q) ->
                   Lim f c <= q
where "r <= q" := (embed r q).

Definition embed_strict `(r : s ->> t, q : u ->> v) := exists i, r <= q[seq i].
Infix " < " := embed_strict (no associativity, at level 70).

(* TODO: define equality based on embed *)

(** Some lemmas on rewrite sequences and relations follow. Most of them are
   analoguous to lemmas on ordinals that can be found in the [Ordinal]
   library. *)

Lemma embed_length :
  forall `(r : s ->> t, q : u ->> v),
    r <= q -> (length r <= length q)%ord.
Proof.
induction r as [t | s t r w p IH | s ts f t c IH]; simpl; intros u v q H.
constructor.
dependent destruction H.
apply Ord_le_Succ with (pred_type_as_pd_type i).
rewrite <- pred_type_as_pd_type_ok.
apply IH.
assumption.
dependent destruction H.
constructor.
intro n.
apply IH.
apply H.
Qed.

Lemma embed_pred_right :
  forall `(r : s ->> t, q : u ->> v, i : pred_type q),
    r <= q[seq i] ->
    r <= q.
Proof.
induction r as [t | s t r w p IH | s ts f t c IH]; intros u v q i H.
constructor.
dependent destruction H.
destruct (pred_trans i i0) as [k T].
revert r p IH H H0.
rewrite <- T.
intros r p IH H H0.
apply Embed_Cons; assumption.
constructor.
intro n.
dependent destruction H.
apply IH with i.
trivial.
Qed.

Lemma embed_pred_left :
  forall `(r : s ->> t, q : u ->> v, i : pred_type r),
    r <= q ->
    r[seq i] <= q.
Proof.
intros s t r u v q i H.
induction H as [s u v q | u v q s j r t p H IH Hp | s ts f t c u v q H IH].
elim i.
destruct i as [[] | i]; apply embed_pred_right with j.
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
destruct i as [[] |]; [| apply embed_pred_right with p0]; assumption.
Qed.

Lemma first_pred_after_cons_id :
  forall `(r : s ->> t, p : t [>] u),
    r = (Cons r p)[seq (inl (pred_type r) tt)].
Proof.
trivial.
Qed.

Lemma embed_cons_left :
  forall `(r : s ->> t, q : v ->> w, p : t [>] u),
    Cons r p <= q ->
    r <= q.
Proof.
intros s t r v w q u p H.
rewrite (first_pred_after_cons_id r) with p.
apply (@embed_pred_left s u (Cons r p) v w q (inl (pred_type r) tt)).
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
apply (@Embed_Cons u w (Cons q p) s (inr _ i) r); assumption.
constructor.
intro n.
apply IH.
dependent destruction H.
trivial.
Qed.

Lemma embed_cons_intro :
  forall `(r : s ->> t, q : u ->> t, p : t [>] v, o : t [>] w),
    r <= q ->
    step_eq p o ->
    Cons r p <= Cons q o.
Proof.
intros.
apply (@Embed_Cons u w (Cons q o) s (inl _ tt) r); assumption.
Qed.

Lemma embed_lim_right :
  forall `(r : s ->> t, f : (forall n, u ->> ts n), c : converges ts v) n,
    r <= f n ->
    r <= Lim f c.
Proof.
induction r as [t | s t r w p _ | s ts f t c IH]; intros u ts' g v c' n H.
constructor.
dependent destruction H.
apply (@Embed_Cons u v (Lim g c') s (existT (fun n => pred_type (g n)) n i) r); assumption.
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
apply Embed_Cons with (q := Cons r p) (i := inl (pred_type r) tt).
assumption.
apply step_eq_refl.
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
induction H1 as [s u v q | u v q s i r t p H IH Hp | s ts f t c u v q H IH]; intros w z x H2.
constructor.
induction H2 as [u w z x | w z x u j q v o H' IH' Ho | u ts' f v c' w z x H' IH'].
destruct i.
destruct i as [[] | i']; simpl in * |- *.
apply Embed_Cons.
apply IH.
assumption.
apply step_eq_trans with (x[1 j]) v o.
assumption.
assumption.
apply embed_pred_right with j.
apply IH'; assumption.
destruct i as [n i]; simpl in * |- *.
apply (IH' n i r p H Hp IH).
constructor.
intro n.
exact (IH n w z x H2).
Qed.

(** This lemma is surprisingly hard to prove directly due to complexities
   with dependent types. Fortunately we can use our results on ordinals with
   the length of rewrite sequences to make a shortcut. *)
Lemma embed_not_cons :
  forall `(r : s ->> t, p : t [>] u),
    ~ Cons r p <= r.
Proof.
intros s t r u p H.
assert (H1 := embed_length H).
contradict H1.
apply ord_le_not_succ.
Qed.

Lemma embed_not_pred_right_strong :
  forall `(r : s ->> t, q : u ->> v, i : pred_type r),
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

Lemma embed_not_pred_right :
  forall `(r : s ->> t, i : pred_type r),
    ~ r <= r[seq i].
Proof.
intros.
apply embed_not_pred_right_strong.
apply embed_refl.
Qed.

Lemma embed_strict_cons_right :
  forall `(r : s ->> t, q : u ->> v, p : v [>] w),
    r < q ->
    r < Cons q p.
Proof.
intros s t r u v q w p.
destruct 1 as [i H].
exists (inl (pred_type q) tt).
apply embed_pred_right with i.
assumption.
Qed.

Lemma embed_strict_embed :
  forall `(r : s ->> t, q : u ->> v),
    r < q ->
    r <= q.
Proof.
intros s t r u v q.
destruct 1 as [i H].
apply embed_pred_right with i.
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
apply embed_trans with u v q; [apply embed_pred_right with i |]; assumption.
Qed.

(** Well-formed rewrite sequences have limit functions [f] where [n < m]
   implies that [f n] is strictly embedded in [f m]. *)
Fixpoint wf s t (r : s ->> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => wf q
  | Lim _ _ f _ _  =>
    (forall n, wf (f n)) /\
    forall n m, (n < m)%nat -> f n < f m
  end.

(** The following convergence definitions are not at all useful. It is
   unclear whether there exist more natural translations of convergence
   to our representation of rewrite sequences. We define some lemmas on
   these definitions below, but have not been able to really work with
   them. *)

(** Weakly convergent sequences have limit functions [f] where for
   any depth [d], from some [n], the end term of [r] is equal up to
   depth [d] where [f n <= r] and [r] is contained in the limit. *)
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

(** Strongly convergent sequences have limit functions [f] where for
   any depth [d], from some [n], the step after [r] is below depth
   [d] where [f n <= r] and [r] is contained in the limit. *)
Fixpoint strongly_convergent `(r : s ->> t) : Prop :=
  weakly_convergent r /\
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => strongly_convergent q
  | Lim _ _ f t _  =>
    (forall n, strongly_convergent (f n)) /\
    forall d, exists n, forall j,
      f n <= r[seq j] ->
      (depth (r[stp j]) > d)%nat
  end.

(** We should probably be able to prove that [weakly_converent] implies
   [strongly_converent]. Note that this is not true in the traditional
   theory of infinitary rewriting, the relevant difference is that we
   have a condition in the definition of rewrite sequences. *)

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

(** Predicate saying that a rewrite sequence is finite. This is useful to
   prove certain properties via a shortcut.

   Maybe it's cleaner to define this via the length of the rewrite
   sequence? *)
Fixpoint finite `(r : s ->> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => finite q
  | Lim _ _ f t c  => False
  end.

(** Finite rewrite sequences are well-formed. *)
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

(** Finite rewrite sequences are weakly convergent. *)
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

(** [snoc] prepends (not appends) a rewrite step to a rewrite sequence. It
   is analoguous to 1 + alpha on ordinals.

   We define [snoc] via an auxiliary function [snoc_rec] to escape some
   type-checker problems (due to [snoc] being recursive in its right
   argument). *)

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

Lemma embed_snoc_right :
  forall `(r : s ->> t, p : u [>] s),
    r <= snoc p r.
Proof.
induction r as [s | s t r v o IH | s ts f t c IH]; intros u p; simpl.
constructor.
apply embed_cons_intro.
apply IH.
apply step_eq_refl.
constructor.
intro n.
apply embed_lim_right with n.
apply IH.
Qed.

Lemma snoc_embed :
  forall `(p : s [>] t, r : t ->> u, q : t ->> v),
    r <= q ->
    snoc p r <= snoc p q.
Proof.
(** This is a very ad-hoc and hairy proof. *)
intros s t p u r v q H.
dependent induction H.
induction q as [t | t v q w o IH | t vs f v c IH]; simpl.
apply embed_refl.
apply embed_cons_right; simpl in IH.
trivial.
apply embed_lim_right with 0; simpl in IH |- *.
trivial.
induction q as [w | w v q z o IH | w vs f v c IH]; simpl.
destruct i.
destruct i as [[] | i].
simpl.
change (Cons (snoc p r) (Cons (snoc p q) p0 [stp inl _ tt]) <= Cons (snoc p q) o).
apply (@Embed_Cons s z (Cons (snoc p q) o) s (inl _ tt) (snoc p r)).
simpl. simpl in IH. simpl in IHembed.
apply IHembed.
assumption.
assumption.
simpl in H. simpl in IH. simpl in IHembed. fold (@pred_type t v) in i.
apply embed_cons_right.
apply IH.
assumption.
assumption.
trivial.
destruct i as [n i].
simpl.
apply embed_lim_right with n.
simpl. simpl in IHembed. simpl in H. simpl in r. fold (pred_type (f n)) in i.
apply IH.
assumption.
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
apply embed_pred_right with i.
assumption.
destruct i as [n i]; simpl in H; fold (pred_type (f n)) in i.
specialize IH with n p r i.
destruct IH as [j IH].
assumption.
exists (existT (fun n => pred_type (snoc p (f n))) n j).
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
assumption.
fold snoc_rec in i.
apply embed_cons_right.
apply IHq; assumption.
destruct i as [n i].
apply embed_lim_right with n.
simpl. (* This is pretty weird, because nothing changes... *)
apply H1; assumption.
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

Lemma snoc_wf :
  forall `(p : s [>] t, r : t ->> u),
    wf r ->
    wf (snoc p r).
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
  forall d x `(p : s [>] t, r : t ->> u, q : t ->> v, j : pred_type (snoc p q)),
    snoc p r <= snoc p q [seq j] ->
    exists i : pred_type q,
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
specialize H with (existT (fun n => pred_type (f n)) m i).
simpl in H.
apply M.
apply H.
apply M.
Qed.

(** [append] concatenates two rewrite sequences. Like [snoc], it is recursive
   in its right argument and defined via a [append_rec] helper function. It
   is the analogue of [add] on ordinals. *)

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
apply Ord_le_Succ with (inl (pd_type (add (length r) (length q))) tt).
apply (IH r).
apply Ord_le_Succ with (inl (pd_type (length (append r q))) tt).
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

Lemma append_embed :
  forall `(r : s ->> t, q : t ->> u, z : t ->> v),
    q <= z ->
    append r q <= append r z.
Proof.
(** So this proof is a verbatim copy of [snoc_embed] an thus is also quite
   hairy and ad-hoc.
   There should be a way to at least not repeat ourselves here. The same
   goes for [snoc_embed_strict] and [append_embed_strict] by the way. *)
intros s t r u q v z H.
dependent induction H.
induction z as [t | t v z w o IH | t vs f v c IH]; simpl.
apply embed_refl.
apply embed_cons_right; simpl in IH.
trivial.
apply embed_lim_right with 0; simpl in IH |- *.
trivial.
induction z as [w | w v z x o IH | w vs f v c IH]; simpl.
destruct i.
destruct i as [[] | i].
simpl.
change (Cons (append r r0) (Cons (append r z) p [stp inl _ tt]) <= Cons (append r z) o).
apply (@Embed_Cons s x (Cons (append r z) o) s (inl _ tt) (append r r0)).
simpl. simpl in IH. simpl in IHembed.
apply IHembed.
assumption.
assumption.
simpl in H. simpl in IH. simpl in IHembed. fold (@pred_type t v) in i.
apply embed_cons_right.
apply IH; assumption.
destruct i as [n i].
simpl.
apply embed_lim_right with n.
simpl. simpl in IHembed. simpl in H. simpl in r. fold (pred_type (f n)) in i.
apply IH; assumption.
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
apply embed_pred_right with i.
assumption.
destruct i as [n i]; simpl in H; fold (pred_type (f n)) in i.
specialize IH with n r q i.
destruct IH as [j IH].
assumption.
exists (existT (fun n => pred_type (append r (f n))) n j).
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

Lemma append_wf :
  forall `(r : s ->> t, q : t ->> u),
    wf r ->
    wf q ->
    wf (append r q).
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

Lemma pred_append :
  forall `(r : s ->> t, q : t ->> u, i : pred_type r),
    exists j : pred_type (append r q),
      append r q [j] = r[i].
Proof.
induction q as [u | t u q v p IH | t us f u c IH]; simpl; intro i.
exists i.
reflexivity.
destruct (IH r i) as [j H].
exists (inr _ j).
assumption.
destruct (IH 0 r i) as [j H].
exists (existT (fun n => pred_type (append r (f n))) 0 j).
assumption.
Qed.

Lemma embed_not_append_pred_left :
  forall `(r : s ->> t, q : t ->> u, j : pred_type r),
    ~ append r q <= r[seq j].
Proof.
induction q; simpl; intros i H1.
contradict H1.
apply embed_not_pred_right.
dependent destruction H1.
destruct (pred_trans i i0) as [j H2].
specialize IHq with r j.
apply IHq.
rewrite H2.
assumption.
dependent destruction H1.
specialize H0 with 0.
contradict H0.
apply H.
Qed.

(** The infinitary unique normal forms property (UN-inf).

   Note that this defines uniqueness of normal forms with respect to
   rewriting, not the more general unique normal forms property. *)

Definition unique_normal_forms : Prop :=
  forall t u v (r : t ->> u) (q : t ->> v),
    wf r ->
    wf q ->
    normal_form u ->
    normal_form v ->
    u [~] v.

End TRS.


Implicit Arguments normal_form [F X].
Implicit Arguments critical_pair [F X].
