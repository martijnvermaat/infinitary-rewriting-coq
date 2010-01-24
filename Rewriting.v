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

(* Rewriting sequences *)
Record sequence : Type := {

  (* Length of rewriting sequence *)
  length : ord;
  length_good : good length;

  (* Projection from ordinals (up to length) to steps *)
  steps : forall alpha, alpha < length -> step;

  (* Successive rewriting steps have equal target/source terms *)
  locally_continuous :
    forall alpha (H : Succ alpha < length),
      target (steps alpha (ord_lt_succ_left alpha length H))
      [~]
      source (steps (Succ alpha) H)

}.

(* Shorthand for source term at step alpha in rewriting sequence s *)
Definition term_at s alpha H := source (steps s alpha H).

(* Shorthand for rewriting depth at step alpha in rewriting sequence s *)
Definition depth_at s alpha H := depth (steps s alpha H).

(* Approaching any limit ordinal < length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_continuous (s : sequence) : Prop :=
  forall f (H1 : Limit f < length s) n,
    exists alpha,
      good alpha /\
      alpha < Limit f /\
      forall beta (H2 : beta < Limit f),
        alpha < beta ->
        term_eq_up_to n (term_at s beta (ord_lt_trans beta (Limit f) (length s) H2 H1))
                        (term_at s (Limit f) H1).

(* Approaching any limit ordinal < length from below,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_continuous (s : sequence) : Prop :=
  forall f (H1 : Limit f < length s) n,
    exists alpha,
      good alpha /\
      alpha < Limit f /\
      forall beta (H2 : beta < Limit f),
        alpha < beta ->
        depth_at s beta (ord_lt_trans beta (Limit f) (length s) H2 H1) > n.

(* The rewriting sequence is weakly continuous, and furthermore,
   if the length of the rewriting sequence is a limit ordinal,
   for all n, eventually terms are equal to each other up to depth n *)
(* NOTE: this implements the notion of cauchy convergence *)
Definition weakly_convergent (s : sequence) : Prop :=
  weakly_continuous s /\
  (* TODO: maybe this should not not use a match construct *)
  match length s with
  | Limit f =>
      forall n,
        exists alpha,
          good alpha /\
          alpha < length s /\
          forall beta gamma (H1 : beta < length s) (H2 : gamma < length s),
            alpha < beta ->
            alpha < gamma ->
            term_eq_up_to n (term_at s beta H1)
                            (term_at s gamma H2)
  | _ => True
  end.

(* The rewriting sequence is strongly continuous, and furthermore,
   if the length of the rewriting sequence is a limit ordinal,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_convergent (s : sequence) : Prop :=
  strongly_continuous s /\
  match length s with
  | Limit f =>
      forall n,
        exists alpha,
          good alpha /\
          alpha < length s /\
          forall beta (H : beta < length s),
            alpha < beta ->
            depth_at s beta H > n
  | _ => True
  end.

(* Strong convergence is only distinct from strong continuity when length is
   a limit ordinal *)
Lemma continuity_implies_convergence_weak :
  forall s,
    weakly_continuous s ->
    ~ weakly_convergent s ->
    exists f, length s = Limit f.
Proof.
intros s CONT CONV.
Admitted.

(* Strong convergence is only distinct from strong continuity when length is
   a limit ordinal *)
Lemma continuity_implies_convergence_weak' :
  forall s,
    match length s with
    | Limit _ => True
    | _       => weakly_continuous s -> weakly_convergent s
    end.
Proof.
intro s.
destruct s as [l s c_local c_limit c_strong]; simpl.
destruct l.
unfold strongly_convergent.
Admitted.

(* Weak convergence is only distinct from weak continuity when length is
   a limit ordinal *)
Lemma continuity_implies_convergence_strong :
  forall s,
    match length s with
    | Limit _ => True
    | _       => strongly_continuous s -> strongly_convergent s
    end.
Proof.
Admitted.

(* Any strongly continuous rewriting sequence is also weakly continuous *)
Lemma strong_continuity_implies_weak_continuity :
  forall s, strongly_continuous s -> weakly_continuous s.
Proof.
Admitted.

(* Any strongly convergent rewriting sequence is also weakly convergent *)
Lemma strong_convergence_implies_weak_convergence :
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

Lemma compression :
  trs_left_linear system ->
  forall s (L : Zero < length s) (SC : strongly_continuous s),
    exists s', exists L' : Zero < length s', exists SC' : strongly_continuous s',
      length s' <= omega /\
      term_at s Zero L [~] term_at s' Zero L' /\
      forall n,
        exists alpha, exists alpha',
          good alpha /\
          good alpha' /\
          alpha < length s /\
          alpha' < length s' /\
          forall beta beta' (H1 : beta < length s) (H2 : beta' < length s'),
            alpha < beta ->
            alpha' < beta' ->
            term_eq_up_to n (term_at s beta H1)
                            (term_at s' beta' H2).
Proof.
Admitted.

Local Close Scope ord_scope.

End TRSs.
