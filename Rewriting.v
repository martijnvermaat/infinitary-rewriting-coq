Require Import prelims.
Require Export List.
Require Export Finite_term.
Require Export Term.
Require Import Substitution.
Require Import Context.
Require Import Ordinals.
Require Import Term_equality.

Section Rules.

Variable F : Signature.
Variable X : Variables.

Notation finite_term := (finite_term F X).

(* Rewriting rules of finite terms *)
Record rule : Type := mkRule {
  lhs     : finite_term;
  rhs     : finite_term;
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

End Rules.


Implicit Arguments rule [F X].
Implicit Arguments lhs [F X].
Implicit Arguments rhs [F X].
Implicit Arguments trs_left_linear [F X].

Section TRSs.

Variable F : Signature.
Variable X : Variables.

Notation term := (term F X).

Variable system : trs F X.

(* Rewriting step *)
Inductive step : Type :=
  | Step : forall r : rule, In r system -> context F X -> substitution F X -> step.

(* Source term of rewriting step *)
Definition source (u : step) : term :=
  match u with
  | Step r H c s => fill c (substitute s (lhs r))
  end.

(* Target term of rewriting step *)
Definition target (u : step) : term :=
  match u with
  | Step r H c s => fill c (substitute s (rhs r))
  end.

(* Depth of rule application in rewriting step *)
Definition depth (u : step) : nat :=
  match u with
  | Step r H c s => hole_depth c
  end.

(* Source and target are equal up to the depth of the rewrite step *)
Lemma eq_up_to_rewriting_depth :
  forall s n,
    depth s > n ->
    term_eq_up_to n (source s) (target s).
Proof.
destruct s.
apply fill_eq_up_to.
Qed.

(* From now on, the default scope is that of our ordinals *)
Local Open Scope ord_scope.

(* NOTE: Here in Rewriting2.v we explicitely list the terms in the sequence.
   This means we always have a first and a last term, but we have to
   explicitely say that the rewriting steps are from and to successive terms
   in the sequence. *)

Axiom ord_le_pi : forall alpha beta (H H' : alpha <= beta), H = H'.
Axiom ord_lt_pi : forall alpha beta (H H' : alpha < beta), H = H'.

(* Rewriting sequences *)
Record sequence : Type := {

  (* Length of rewriting sequence *)
  length : ord;

  (* Projection from ordinals (up to and including length) to terms *)
  terms : forall alpha, alpha <= length -> term;

  (* Projection from ordinals (up to length) to steps *)
  steps : forall alpha, alpha < length -> step;

  local_continuity :
    forall alpha (H : alpha < length),
      source (steps alpha H) [=] terms alpha (ord'_lt_ord'_le H) /\
      target (steps alpha H) [=] terms (succ alpha) (ord'_lt_ord'_le_succ H)

}.

Definition distance_decreasing (s : sequence) (lambda : ord) (Hl : lambda <= length s) : Prop :=
  forall n,
    exists alpha,
      good alpha /\
      alpha < lambda /\
      forall beta (Hb : beta < lambda),
        alpha < beta ->
        term_eq_up_to n (terms s beta (ord_le_trans beta lambda (length s)
                                                    (ord_lt_ord_le beta lambda Hb) Hl))
                        (terms s lambda Hl).

Definition depth_increasing (s : sequence) (lambda : ord) (Hl : lambda <= length s) : Prop :=
  forall n,
    exists alpha,
      good alpha /\
      alpha < lambda /\
      forall beta (Hb : beta < lambda),
        alpha < beta ->
        depth (steps s beta (ord_lt_trans_le_right beta lambda (length s) Hb Hl)) > n.

(* Approaching any limit ordinal < length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_continuous (s : sequence) : Prop :=
  forall lambda (Hl : lambda < length s),
    is_limit lambda ->
    distance_decreasing s lambda (ord_lt_ord_le lambda (length s) Hl).

(* Approaching any limit ordinal < length from below,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_continuous (s : sequence) : Prop :=
  weakly_continuous s /\
  forall lambda (Hl : lambda < length s),
    is_limit lambda ->
    depth_increasing s lambda (ord_lt_ord_le lambda (length s) Hl).

(* Approaching any limit ordinal <= length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_convergent (s : sequence) : Prop :=
  forall lambda (Hl : lambda <= length s),
    is_limit lambda ->
    distance_decreasing s lambda Hl.

(* Approaching any limit ordinal <= length from below,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_convergent (s : sequence) : Prop :=
  weakly_convergent s /\
  forall lambda (Hl : lambda <= length s),
    is_limit lambda ->
    depth_increasing s lambda Hl.

Lemma locally_convergent_succ_elim :
  forall
    (s_length : ord)
    (s_terms : (forall alpha : ord, alpha <= Succ s_length -> term))
    (s_steps : (forall alpha : ord, alpha < Succ s_length -> step))
    (LC : (forall (alpha : ord) (H : alpha < Succ s_length),
      source (s_steps alpha H) [=]
        s_terms alpha (ord_lt_ord_le alpha (Succ s_length) H) /\
      target (s_steps alpha H) [=]
        s_terms (Succ alpha) (ord_lt_ord_le_succ alpha (Succ s_length) H))),
    (forall (alpha : ord) (H : alpha < s_length),
      source (s_steps alpha (ord_lt_succ_right alpha s_length H)) [=]
        s_terms alpha (ord_le_succ_right alpha s_length (ord_lt_ord_le alpha s_length H)) /\
      target (s_steps alpha (ord_lt_succ_right alpha s_length H)) [=]
        s_terms (Succ alpha)(ord_le_succ_right (Succ alpha) s_length (ord_lt_ord_le_succ alpha s_length H))).
Proof.
intros.
rewrite
  (ord_le_pi alpha (Succ s_length)
    (ord_le_succ_right alpha s_length (ord_lt_ord_le alpha s_length H))
    (ord_lt_ord_le alpha (Succ s_length) (ord_lt_succ_right alpha s_length H))).
rewrite
  (ord_le_pi (Succ alpha) (Succ s_length)
    (ord_le_succ_right (Succ alpha) s_length (ord_lt_ord_le_succ alpha s_length H))
    (ord_lt_ord_le_succ alpha (Succ s_length) (ord_lt_succ_right alpha s_length H))).
exact (LC alpha (ord_lt_succ_right alpha s_length H)).
Qed.

Lemma strongly_convergent_succ_elim :
  forall
    (s_length : ord)
    (s_length_good : good s_length)
    (s_terms : (forall alpha : ord, alpha <= Succ s_length -> term))
    (s_steps : (forall alpha : ord, alpha < Succ s_length -> step))
    (LC : (forall alpha (H : alpha < Succ s_length),
      source (s_steps alpha H) [=] s_terms alpha (ord_lt_ord_le alpha (Succ s_length) H) /\
      target (s_steps alpha H) [=] s_terms (Succ alpha) (ord_lt_ord_le_succ alpha (Succ s_length) H)))
    (SC : strongly_convergent (Build_sequence (Succ s_length) s_length_good s_terms s_steps LC)),
    strongly_convergent (Build_sequence
      s_length
      (good_succ_elim s_length s_length_good)
      (fun alpha H => (s_terms alpha (ord_le_succ_right alpha s_length H)))
      (fun alpha H => (s_steps alpha (ord_lt_succ_right alpha s_length H)))
      (locally_convergent_succ_elim s_length s_terms s_steps LC)).
Proof.
intros.
unfold strongly_convergent.
split.
unfold weakly_convergent.
Admitted.

Lemma compression :
  trs_left_linear system ->
  forall s,
    strongly_convergent s ->
    exists s',
      strongly_convergent s' /\
      length s' <= omega /\
      terms s Zero (Ord_le_Zero (length s))
        [=] terms s' Zero (Ord_le_Zero (length s')) /\
      terms s (length s) (ord_le_refl (length s))
        [=] terms s' (length s') (ord_le_refl (length s')).
Proof.
intros LL s SC.
destruct s as [s_length LG s_terms s_steps LC].
induction s_length as [| s_length IH | f IH].

(* length s = Zero *)
exists (Build_sequence Zero LG s_terms s_steps LC).
split.
assumption.
split.
apply Ord_le_Zero.
split; apply term_eq_refl.

(* length s = Succ _ *)
(* Apply IH for first s_length segment *)

assert (IH' := IH
  (good_succ_elim s_length LG)
  (fun alpha H => (s_terms alpha (ord_le_succ_right alpha s_length H)))
  (fun alpha H => (s_steps alpha (ord_lt_succ_right alpha s_length H)))
  (locally_convergent_succ_elim s_length s_terms s_steps LC)
  (strongly_convergent_succ_elim s_length LG s_terms s_steps LC SC)).
elim IH'.
intros.
(* gevalsonderscheid voor length x <= omega: < omega of = omega *)
admit.

(* length s = Limit _ *)
admit.

Qed.

Local Close Scope ord_scope.

End TRSs.
