Require Import prelims.
Require Export List.
Require Export Finite_term.
Require Export Term.
Require Import Substitution.
Require Import Context.
Require Export PreOrdinals.
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

(*
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
*)

Generalizable All Variables.

Reserved Notation "s [>] t" (no associativity, at level 40).

Inductive step : term -> term -> Type :=
| Step : forall (s t : term) (r : rule), s [>] t
where "s [>] t" := (step s t).

Reserved Notation "s -[ l ]-> t" (no associativity, at level 40).

Inductive sequence : term -> term -> ord' -> Type :=
| Nil   : forall t, t -[Zero]-> t
| Cons  : forall `{r : s -[l]-> t, p : t [>] u}, s -[Succ l]-> u
| Lim   : forall (p : nat -> term) (l : nat -> ord') s (f : (forall n : nat, s -[l n]-> p n)) t,
            (forall n, exists m, term_eq_up_to n (p m) t) -> s -[Limit l]-> t
where "s -[ l ]-> t" := (sequence s t l).

(*
   NOTES:

   Or don't include length in type, define it by recursion

   Does this definition include exactly weak convergence?

   The limit case consists of infinitely many sequences (of which
   we should demand that they are increasing in length), but
   they are only related by the first term. What does this mean?
*)

Definition Omega := Limit id.

(*
Lemma compression :
  trs_left_linear system ->
  forall r : s -[l]-> t,
    strongly_convergent r ->
    exists r' : s -[l']-> t,
      strongly_convergent r' /\
      l' <= Omega.
*)


End TRSs.
