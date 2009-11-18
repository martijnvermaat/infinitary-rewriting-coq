Require Import List.
Require Export Finite_term.
Require Export Term.
Require Import Substitution.
Require Import Ordinals.


Section Rules.

Variable F : Signature.

Notation finite_term := (finite_term F).

(* Rewriting rules of finite terms *)
Record rule : Type := {
  lhs     : finite_term;
  rhs     : finite_term;
  rule_wf : not (is_var lhs) /\ incl (vars rhs) (vars lhs)
}.

(* Left hand side is linear *)
Definition left_linear (r : rule) : Prop :=
  linear (lhs r).

(* A Term Rewriting System as a finite list of of rewriting rules *)
Definition trs := list rule.

(* All rules are left-linear *)
Fixpoint left_linear_trs (s : trs) : Prop :=
  match s with
  | nil   => True
  | r::rs => left_linear r /\ left_linear_trs rs
  end.

End Rules.


Implicit Arguments rule [F].
Implicit Arguments lhs [F].
Implicit Arguments rhs [F].
Implicit Arguments left_linear_trs [F].


Section TRSs.

Variable F : Signature.

Notation term := (term F).

Variable system : trs F.

(*
(* Rewriting step *)
Inductive step : Type :=
  | Step : forall r : rule, In r system -> context F -> substitution F -> step.

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

Variable term_bis : term -> term -> Prop.

(* From now on, the default scope is that of our ordinals *)
Local Open Scope ordinals_scope.

(* Strongly continuous rewriting sequences *)
Record sequence : Type := {

  (* Length of rewriting sequence *)
  length : Ord;

  (* Projection from ordinals (up to length) to steps *)
  steps : forall a : Ord, a < length -> step;

  (* Successive rewriting steps have equal target/source terms *)
  continuous_local :
    forall a : Ord,
    forall H : succ a < length,
    term_bis (target (steps a (lt_invariant_succ a length H)))
             (source (steps (succ a) H));

  (* Approaching any limit ordinal a < length from below,
     for all n, eventually terms are equal to the limit term up to depth n *)
  continuous_limit :
    forall a : Ord, limit a ->
    forall H1 : a < length,
    forall n : nat,
    exists b, b < a /\
      forall c, b < c -> forall H2 : c < a,
      equal_up_to n (source (steps c (lt_trans c a length H2 H1)))
                    (source (steps a H1));

  (* Approaching any limit ordinal < length from below,
     for all n, eventually the rule applications are below depth n *)
  continuous_strong :
    forall a : Ord, limit a ->
    forall H1 : a < length,
    forall n : nat,
    exists b, b < a /\
      forall c, b < c -> forall H2 : c < a,
      depth (steps c (lt_trans c a length H2 H1)) > n
}.

(* Shorthand for reaching source term at step a in rewriting sequence s *)
Definition term_at s (a : Ord) H := source (steps s a H).

(* If the length of the rewriting sequence is a limit ordinal,
   for all n, eventually terms are equal up to depth n *)
Definition weakly_convergent (s : sequence) : Prop :=
  limit (length s) ->
  forall n : nat,
  exists b, b < length s /\
    forall c d, b < c -> b < d ->
    forall H1 : c < length s, forall H2 : d < length s,
    equal_up_to n (term_at s c H1)
                  (term_at s d H2).

(* If the length of the rewriting sequence is a limit ordinal,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_convergent (s : sequence) : Prop :=
  limit (length s) ->
  forall n : nat,
  exists b, b < length s /\
    forall c, b < c -> forall H : c < length s,
    depth (steps s c H) > n.

(* Any strongly convergent rewriting sequence is also weakly convergent *)
Lemma strong_implies_weak : forall s, strongly_convergent s -> weakly_convergent s.
Proof.
Admitted.

(* Assume we can get a limit term for any weakly convergent rewriting sequence *)
(* TODO: This would be a fixpoint using b from weakly_convergent *)
Variable limit_term : forall s : sequence, weakly_convergent s -> term.

Lemma compression : left_linear_trs system -> forall s : sequence,
                    forall SC: strongly_convergent s,
                    exists s' : sequence,
                    exists SC' : strongly_convergent s',
                      length s' < omega /\ (* should be <= *)
                      term_bis (limit_term s (strong_implies_weak s SC)) (limit_term s' (strong_implies_weak s' SC')).
Proof.
Admitted.

Local Close Scope ordinals_scope.

End TRSs.
*)
