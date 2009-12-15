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
simpl.
intros n H.
apply fill_eq_up_to.
assumption.
Qed.

(* From now on, the default scope is that of our ordinals *)
Local Open Scope ord_scope.

(* TODO

Should we include the limit term in the sequence record?

If the length of the sequence is l, then the limit term would be the term
at position l in the sequence.

l = Zero    : we should have no limit term
l = Succ l' : limit term should be the target of step l'
l = Lim f   : limit term lets us define weak convergence?

Maybe a better way:

Not include the limit term (sequences might not have one), and define
weak convergence as 'there exists a limit term t and ... t ...'

Then we would have to construct the limit, using a property like
'approaching the end of the sequence, terms get equal up to any depth'

This is basically what we now use as definition of weak convergence, but
than we could use a more direct translation of the literature using the
constructed limit.

See also the definitions by Kennaway.

*)

(* Strongly continuous rewriting sequences *)
Record sequence : Type := {

  (* TODO: maybe we should include the limit term, this would help
     to give a more direct definition of weakly_convergent *)

  (* Length of rewriting sequence *)
  length : ord;

  (* Projection from ordinals (up to length) to steps *)
  steps : forall alpha, alpha < length -> step;

  (* Successive rewriting steps have equal target/source terms *)
  continuous_local :
    forall alpha (H : Succ alpha < length),
      target (steps alpha (ord_lt_succ_left alpha length H))
      [~]
      source (steps (Succ alpha) H);

  (* Approaching any limit ordinal < length from below,
     for all n, eventually terms are equal to the limit term up to depth n *)
  continuous_limit :
    forall f (H1 : Limit f < length) n,
      exists alpha,
        alpha < Limit f /\
        forall beta (H2 : beta < Limit f),
          alpha < beta ->
          term_eq_up_to n (source (steps beta (ord_lt_trans beta (Limit f) length H2 H1)))
                          (source (steps (Limit f) H1));

  (* Approaching any limit ordinal < length from below,
     for all n, eventually the rule applications are below depth n *)
  continuous_strong :
    forall f (H1 : Limit f < length) n,
      exists alpha,
        alpha < Limit f /\
        forall beta (H2 : beta < Limit f),
          alpha < beta ->
          depth (steps beta (ord_lt_trans beta (Limit f) length H2 H1)) > n

}.

(* Shorthand for reaching source term at step a in rewriting sequence s *)
(* TODO: if we include limit term in sequences, alpha may be <= the length *)
Definition term_at s alpha H := source (steps s alpha H).

(* If the length of the rewriting sequence is a limit ordinal,
   for all n, eventually terms are equal up to depth n *)
Definition weakly_convergent (s : sequence) : Prop :=
  match length s with
  | Limit f =>
    forall n,
      exists b,
        b < length s /\
        forall c d (H1 : c < length s) (H2 : d < length s),
          b < c ->
          b < d ->
          term_eq_up_to n (term_at s c H1)
                          (term_at s d H2)
  | _ => True
  end.

(* If the length of the rewriting sequence is a limit ordinal,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_convergent (s : sequence) : Prop :=
  match length s with
  | Limit f =>
    forall n,
      exists b,
        b < length s /\
        forall c (H : c < length s),
          b < c ->
          depth (steps s c H) > n
  | _ => True
  end.

(* Convergence is only distinct from continuity when length is a limit ordinal *)
(* TODO: think about right definitions for limit term and weak convergence *)
(*
Lemma length_no_limit_continuity_implies_convergence :
  forall s,
    match length s with
    | Zero    => strongly_convergent s
    | Succ _  => strongly_convergent s
    | Limit _ => True
    end.
Proof.
intro s.
destruct s as [l s c_local c_limit c_strong]; simpl.
destruct l.
unfold strongly_convergent.
*)

(* Any strongly convergent rewriting sequence is also weakly convergent *)
(* TODO *)
Lemma strong_implies_weak :
  forall s, strongly_convergent s -> weakly_convergent s.
Proof.
(*
intros s Hstrong' Hlimit n.
assert (Hstrong := Hstrong' Hlimit n). clear Hstrong'.
elim Hstrong.
intros.
exists x.
split.
apply H.
intros c d LTxc LTxd LTcl LTdl.
destruct H as [H1 H2].
*)
(* Do something with eq_up_to_rewriting_depth *)
Admitted.

(* Assume we can get a limit term for any weakly convergent rewriting sequence *)
(* TODO: This would be a fixpoint using b from weakly_convergent *)
Variable limit_term : forall s : sequence, weakly_convergent s -> term.

(* TODO: define omega *)
Variable omega : ord.

Lemma compression :
  trs_left_linear system ->
  forall s (SC : strongly_convergent s),
    exists s', exists SC' : strongly_convergent s',
      length s' <= omega /\
        limit_term s (strong_implies_weak s SC)
        [~]
        limit_term s' (strong_implies_weak s' SC').
Proof.
Admitted.

Local Close Scope ord_scope.

End TRSs.
