(* Inductive defintion for rewriting sequences *)


Require Import Prelims.
Require Export List.
Require Export FiniteTerm.
Require Export Term.
Require Import Substitution.
Require Import Context.
Require Export PreOrdinal.
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

(* Only needed in Coq 8.3 *)
(* Generalizable All Variables. *)

Reserved Notation "s [>] t" (no associativity, at level 40).

Inductive step : term -> term -> Type :=
  | Step : forall (r : rule) (c : context) (s : substitution),
             In r system ->
             fill c (substitute s (lhs r)) [>] fill c (substitute s (rhs r))
where "s [>] t" := (step s t).

(* Depth of rule application in rewriting step *)
Definition depth s t (r : s [>] t) : nat :=
  match r with
  | Step _ c _ _ => hole_depth c
  end.

(* Source and target are equal up to the depth of the rewrite step *)
Lemma eq_up_to_rewriting_depth :
  forall `{r : s [>] t} n,
    depth r > n ->
    term_eq_up_to n s t.
Proof.
destruct r.
apply fill_eq_up_to.
Qed.

(* Only needed in Coq 8.3 *)
(*Generalizable All Variables.*)

Reserved Notation "s --> t" (no associativity, at level 40).

Inductive sequence : term -> term -> Type :=
  | Nil   : forall t, t --> t
  | Cons  : forall `{r : s --> t, p : t [>] u}, s --> u
  | Lim   : forall s (p : nat -> term) (f : (forall n : nat, s --> p n)) t, s --> t
where "s --> t" := (sequence s t).

Implicit Arguments Cons [s t u].

Fixpoint length t s (r : t --> s) : ord' :=
  match r with
  | Nil _          => Zero
  | Cons _ _ r _ _ => Succ (length r)
  | Lim _ _ f _    => Limit (fun n => length (f n))
  end.

Fixpoint pref_type t s (r : t --> s) : Type :=
  match r with
  | Nil _          => False
  | Cons _ _ r _ _ => (unit + pref_type r) % type
  | Lim _ _ f _    => { n : nat & pref_type (f n) }
  end.

Fixpoint pref t s (r : t --> s) : pref_type r -> {s' : term & t --> s'} :=
  match r in t --> s return pref_type r -> {s' : term & t --> s'} with
  | Nil _           => False_rect _
  | Cons t s' q _ _ => fun i => match i with
                               | inl tt => existT (fun u => t --> u) s' q
                               | inr t  => pref q t
                               end
  | Lim   _ _ f _  => fun i => match i with
                               | existT n t => pref (f n) t
                               end
  end.

Inductive prefix : forall s t u, (s --> t) -> (s --> u) -> Prop :=
  Pref : forall s t (r : s --> t) (i : pref_type r), prefix (projT2 (pref r i)) r.


  (* Another try *)

Inductive prefix : forall s t u, (s --> t) -> (s --> u) -> Prop :=
  | PrefNil  : forall `{r : s --> t}, prefix r r
  | PrefCons : forall `{r : s --> t, q : s --> v, p : v [>] u}, prefix r q -> prefix r (Cons q p)
  | PrefLim  : forall `{r : s --> t, q : s --> v, p : nat -> term, f : (forall n : nat, s --> p n), u},
                 (exists n, p n = v /\ f n = q) -> prefix r q -> prefix r (Lim p f u).


Definition Omega := Limit (fun n => n).

Lemma compression :
  trs_left_linear system ->
  forall r : s --> t,
    strongly_convergent r ->
    exists r' : s --> t,
      strongly_convergent r' /\
      length r' <= Omega.

End TRS.
