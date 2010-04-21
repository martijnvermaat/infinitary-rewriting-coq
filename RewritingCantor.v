Add LoadPath "../Cantor/prelude".
Add LoadPath "../Cantor/misc".
Add LoadPath "../Cantor/rpo".
Add LoadPath "../Cantor/epsilon0".
Add LoadPath "../Cantor/gamma0".


Require Import Prelims.
Require Import List.
Require Export FiniteTerm.
Require Export Term.
Require Import Substitution.
Require Import Context.
Require Export TermEquality.
Require Export EPSILON0.


Set Implicit Arguments.


Section Rule.

Variable S : signature.
Variable X : variables.

Notation fterm := (finite_term S X).

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


Implicit Arguments rule [S X].


Section TRS.

Variable S : signature.
Variable X : variables.

Notation term := (term S X).
Notation context := (context S X).
Notation substitution := (substitution S X).
Notation trs := (trs S X).

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
    (n <= depth s)%nat ->
    term_eq_up_to n (source s) (target s).
Proof.
destruct s.
apply fill_eq_up_to.
Qed.

(* NOTE: Here in Rewriting2.v we explicitely list the terms in the sequence.
   This means we always have a first and a last term, but we have to
   explicitely say that the rewriting steps are from and to successive terms
   in the sequence. *)

(*Set Strongly Strict Implicit.*)
Unset Implicit Arguments.

(* Rewriting sequences *)
(* TODO: pi for steps/terms? *)
Record sequence : Type := Sequence {

  length : T1;
  nf_length : nf length;

  terms : forall alpha, nf alpha -> alpha <= length -> term;

  steps : forall alpha, nf alpha -> alpha < length -> step;

  local_continuity :
    forall alpha (nf_alpha : nf alpha) (H : alpha < length),
      source (steps alpha nf_alpha H) [=] terms alpha nf_alpha (or_intror _ H) /\
      target (steps alpha nf_alpha H) [=] terms (succ alpha) (succ_nf nf_alpha) (lt_succ_le nf_alpha nf_length H)

  (* terms_pi : forall alpha H H', terms alpha H = terms alpha H'; *)
  (* steps_pi : forall alpha H H', steps alpha H = steps alpha H'; *)

}.

(* Implicit Arguments terms_pi [alpha]. *)
(* Implicit Arguments steps_pi [alpha]. *)

Definition distance_decreasing (s : sequence) (lambda : T1) (nf_lambda : nf lambda) (Hl : lambda <= length s) : Prop :=
  forall n,
    exists alpha,
      alpha < lambda /\
      forall beta (nf_beta : nf beta) (Hb : beta < lambda),
        alpha < beta ->
        term_eq_up_to n (terms s beta nf_beta (or_intror _ (lt_le_trans Hb Hl)))
                        (terms s lambda nf_lambda Hl).

Definition depth_increasing (s : sequence) (lambda : T1) (nf_lambda : nf lambda) (Hl : lambda <= length s) : Prop :=
  forall n,
    exists alpha,
      alpha < lambda /\
      forall beta (nf_beta : nf beta) (Hb : beta < lambda),
        alpha < beta ->
        depth (steps s beta nf_beta (lt_le_trans Hb Hl)) > n.

(* cons a n b represents  omega^a *(S n)  + b *)
Fixpoint is_limit alpha : Prop :=
  match alpha with
  | zero          => False
  | cons zero _ _ => False
  | cons _    _ b => is_limit b
  end.

(* Approaching any limit ordinal < length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_continuous (s : sequence) : Prop :=
  forall lambda (nf_lambda : nf lambda) (Hl : lambda < length s),
    is_limit lambda ->
    distance_decreasing s lambda nf_lambda (or_intror _ Hl).

(* Approaching any limit ordinal < length from below,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_continuous (s : sequence) : Prop :=
  weakly_continuous s /\
  forall lambda (nf_lambda : nf lambda) (Hl : lambda < length s),
    is_limit lambda ->
    depth_increasing s lambda nf_lambda (or_intror _ Hl).

(* Approaching any limit ordinal <= length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_convergent (s : sequence) : Prop :=
  forall lambda (nf_lambda : nf lambda) (Hl : lambda <= length s),
    is_limit lambda ->
    distance_decreasing s lambda nf_lambda Hl.

(* Approaching any limit ordinal <= length from below,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_convergent (s : sequence) : Prop :=
  weakly_convergent s /\
  forall lambda (nf_lambda : nf lambda) (Hl : lambda <= length s),
    is_limit lambda ->
    depth_increasing s lambda nf_lambda Hl.

End TRS.
