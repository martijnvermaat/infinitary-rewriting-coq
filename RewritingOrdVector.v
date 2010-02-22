Require Import prelims.
Require Export List.
Require Export Finite_term.
Require Export Term.
Require Import Substitution.
Require Import Context.
Require Export Ordinals.
Require Export OrdVector.
Require Export Term_equality.


Set Implicit Arguments.


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


Section TRSs.

Variable F : Signature.
Variable X : Variables.

Notation term := (term F X).
Notation rule := (rule F X).

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
Local Open Scope ord'_scope.
Local Open Scope ord_scope.

Set Strongly Strict Implicit.

(* Rewriting sequences *)
Record sequence : Type := Sequence {

  (* Length of rewriting sequence *)
  length : ord';

  (* Projection from ordinals (up to and including length) to terms *)
  (* TODO: number of terms should be length+1 (or limit) *)
  (* IDEA: only include last_term *)
  terms : ovector term length;

  (* Projection from ordinals (up to length) to steps *)
  steps : ovector step length;

  locally_continuous :
    forall alpha : pred_type length,
      source (steps alpha) [=] terms alpha /\
      target (steps alpha) [=] terms alpha

}.

Unset Strongly Strict Implicit.

Definition distance_decreasing (s : sequence) (lambda : pred_type (length s)) : Prop :=
  forall n,
    exists alpha,
      alpha <' pred (length s) lambda /\
      forall beta : pred_type (length s),
        pred (length s) beta <' pred (length s) lambda ->
        alpha <' pred (length s) beta ->
        term_eq_up_to n (terms s beta) (terms s lambda).

Definition depth_increasing (s : sequence) (lambda : ord) : Prop :=
  forall n,
    exists alpha,
      alpha < lambda /\
      forall beta,
        beta < lambda ->
        alpha < beta ->
        depth (steps s beta) > n.

(* Approaching any limit ordinal < length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_continuous (s : sequence) : Prop :=
  forall lambda,
    is_limit lambda ->
    lambda < length s ->
    distance_decreasing s lambda.

(* Approaching any limit ordinal < length from below,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_continuous (s : sequence) : Prop :=
  weakly_continuous s /\
  forall lambda,
    is_limit lambda ->
    lambda < length s ->
    depth_increasing s lambda.

(* Approaching any limit ordinal <= length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_convergent (s : sequence) : Prop :=
  forall lambda,
    is_limit lambda ->
    lambda <= length s ->
    distance_decreasing s lambda.

(* Approaching any limit ordinal <= length from below,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_convergent (s : sequence) : Prop :=
  weakly_convergent s /\
  forall lambda,
    is_limit lambda ->
    lambda <= length s ->
    depth_increasing s lambda.

Local Close Scope ord_scope.
Local Close Scope ord'_scope.

End TRSs.
