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

(* NOTE: Here in Rewriting2.v we explicitely list the terms in the sequence.
   This means we always have a first and a last term, but we have to
   explicitely say that the rewriting steps are from and to successive terms
   in the sequence. *)

(* Rewriting sequences *)
Record sequence : Type := {

  (* Length of rewriting sequence *)
  length : ord;
  length_good : good length;

  (* Projection from ordinals (up to and including length) to terms *)
  terms : forall alpha, alpha <= length -> term;

  (* Projection from ordinals (up to length) to steps *)
  steps : forall alpha, alpha < length -> step;

  steps_fit :
    forall alpha (H : alpha < length),
      source (steps alpha H) [=] terms alpha (ord_lt_ord_le alpha length H) /\
      target (steps alpha H) [=] terms (Succ alpha) (ord_lt_ord_le_succ alpha length H)

}.

(* Approaching any limit ordinal < length from below,
   for all n, eventually terms are equal to the limit term up to depth n *)
Definition weakly_continuous (s : sequence) : Prop :=
  forall f (Hf : Limit f < length s) n,
    exists alpha,
      good alpha /\
      alpha < Limit f /\
      forall beta (Hb : beta < Limit f),
        alpha < beta ->
        term_eq_up_to n (terms s beta (ord_lt_ord_le beta (length s) (ord_lt_trans beta (Limit f) (length s) Hb Hf)))
                        (terms s (Limit f) (ord_lt_ord_le (Limit f) (length s) Hf)).

(* Approaching any limit ordinal < length from below,
   for all n, eventually the rule applications are below depth n *)
(* NOTE: we really also need weakly_continuous in this definition,
   otherwise we lose 'connection' between terms before a limit
   position and the term at that limit position. *)
Definition strongly_continuous (s : sequence) : Prop :=
  weakly_continuous s /\
  forall f (Hf : Limit f < length s) n,
    exists alpha,
      good alpha /\
      alpha < Limit f /\
      forall beta (Hb : beta < Limit f),
        alpha < beta ->
        depth (steps s beta (ord_lt_trans beta (Limit f) (length s) Hb Hf)) > n.

(* The rewriting sequence is weakly continuous, and furthermore,
   if the length of the rewriting sequence is a limit ordinal,
   for all n, eventually terms are equal to each other up to depth n *)
Definition weakly_convergent (s : sequence) : Prop :=
  weakly_continuous s /\
  (is_limit (length s) ->
    forall n,
      exists alpha,
        good alpha /\
        alpha < length s /\
        forall beta (Hb : beta < length s),
          alpha < beta ->
          term_eq_up_to n (terms s beta (ord_lt_succ_left beta (length s) Hb))
                          (terms s (length s) ?).

(* The rewriting sequence is strongly continuous, and furthermore,
   if the length of the rewriting sequence is a limit ordinal,
   for all n, eventually the rule applications are below depth n *)
Definition strongly_convergent (s : sequence) : Prop :=
  strongly_continuous s /\
  (is_limit (length s) ->
    forall n,
      exists alpha,
        good alpha /\
        alpha < length s /\
        forall beta (Hb : beta < length s),
          alpha < beta ->
          depth (steps s beta Hb) > n).

(* Any strongly convergent rewriting sequence is also weakly convergent *)
Lemma strong_convergence_implies_weak_convergence :
  forall s, strongly_convergent s -> weakly_convergent s.
Proof.
intros s s_conv.
destruct s_conv as [[w_cont s_cont] s_conv].
split.
exact w_cont.
intros limit n.
elim (s_conv limit n).
intros alpha H.
destruct H as [Ha' [Ha H]].
exists alpha.
split.
exact Ha'.
split.
exact Ha.
(* NOTE: zouden we de oude definitie voor weakly_convergent (zie comments boven),
   dan werd dit een ingewikkelder verhaal, iets als inductie op verschil tussen
   beta en gamma (liefst eindig, maar daarvoor moet alpha stricter):
   0: beta en gamma zijn gelijk
   1: gebruik eq_up_to_rewriting_depth
   n+1: gebruik eq_up_to_rewriting depth en IH met transitiviteit van term_eq_up_to *)
intros beta Hb Hab.
apply term_eq_up_to_trans with (target (steps s beta (ord_lt_succ_left beta (length s) Hb))).
apply eq_up_to_rewriting_depth.
apply H.
exact Hab.
apply locally_continuous.
Qed.

(*
   TODO:
   * notion of concatenating rewriting sequences
   * what does it mean that our sequences of length 0 have no term?
     (e.g. we need the L predicate in the compression lemma below)
*)
Lemma compression :
  trs_left_linear system ->
  forall s (L : Zero < length s),
    strongly_convergent s ->
    exists s', exists L' : Zero < length s',
      strongly_convergent s' /\
      length s' <= omega /\
      term_at s Zero L [~] term_at s' Zero L' /\
      forall n,
        exists alpha, exists alpha',
          good alpha /\
          good alpha' /\
          alpha < length s /\
          alpha' < length s' /\
          forall beta beta' (Hb : beta < length s) (Hb' : beta' < length s'),
            alpha < beta ->
            alpha' < beta' ->
            term_eq_up_to n (term_at s beta Hb)
                            (term_at s' beta' Hb').
Proof.
intros LL s s_nonzero s_conv.
destruct s as [s_length s_length_good s_steps s_cont].
induction s_length as [| s_length IH | f IH].

(* length s = Zero *)
unfold length in s_nonzero.
contradict (ord_le_zero_zero s_nonzero).

(* length s = Succ _ *)
admit.

(* length s = Limit _ *)
admit.

Qed.

Local Close Scope ord_scope.

End TRSs.
