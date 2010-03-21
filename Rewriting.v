Require Import Prelims.
Require Export List.
Require Export FiniteTerm.
Require Export Term.
Require Import Substitution.
Require Import Context.
Require Export Ordinal.
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

(* Rewriting step *)
Inductive step : Type :=
  | Step : forall r : rule, In r system -> context -> substitution -> step.

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
    n <= depth s ->
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

Set Strongly Strict Implicit.

(* Rewriting sequences *)
Record sequence : Type := Sequence {

  (* Length of rewriting sequence *)
  length : ord;

  (* Projection from ordinals (up to and including length) to terms *)
  terms : forall alpha, alpha <= length -> term;

  terms_pi : forall alpha H H', terms alpha H = terms alpha H';

  (* Projection from ordinals (up to length) to steps *)
  steps : forall alpha, alpha < length -> step;

  steps_pi : forall alpha H H', steps alpha H = steps alpha H';

  local_continuity :
    forall alpha (H : alpha < length),
      source (steps alpha H) [=] terms alpha (ord'_lt_ord'_le H) /\
      target (steps alpha H) [=] terms (succ alpha) (ord'_lt_ord'_le_succ H)

}.

Implicit Arguments terms_pi [alpha].
Implicit Arguments steps_pi [alpha].

Definition distance_decreasing (s : sequence) (lambda : ord) (Hl : lambda <= length s) : Prop :=
  forall n,
    exists alpha,
      alpha < lambda /\
      forall beta (Hb : beta < lambda),
        alpha < beta ->
        term_eq_up_to n (terms s beta (ord'_le_trans (ord'_lt_ord'_le Hb) Hl))
                        (terms s lambda Hl).

Definition depth_increasing (s : sequence) (lambda : ord) (Hl : lambda <= length s) : Prop :=
  forall n,
    exists alpha,
      alpha < lambda /\
      forall beta (Hb : beta < lambda),
        alpha < beta ->
        depth (steps s beta (ord'_lt_trans_ord'_le_right Hb Hl)) > n.

(* Approaching any limit ordinal < length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_continuous (s : sequence) : Prop :=
  forall lambda (Hl : lambda < length s),
    is_limit lambda ->
    distance_decreasing s lambda (ord'_lt_ord'_le Hl).

(* Approaching any limit ordinal < length from below,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_continuous (s : sequence) : Prop :=
  weakly_continuous s /\
  forall lambda (Hl : lambda < length s),
    is_limit lambda ->
    depth_increasing s lambda (ord'_lt_ord'_le Hl).

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

Local Close Scope ord_scope.

End TRS.
