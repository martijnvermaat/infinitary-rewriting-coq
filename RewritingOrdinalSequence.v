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
(*Generalizable All Variables.*)

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
  forall `(r : s [>] t) n,
    depth r > n ->
    term_eq_up_to n s t.
Proof.
destruct r.
apply fill_eq_up_to.
Qed.

Reserved Notation "s --> t" (no associativity, at level 40).

Inductive sequence : term -> term -> Type :=
  | Nil   : forall t, t --> t
  | Cons  : forall `(r : s --> t, p : t [>] u), s --> u
  | Lim   : forall s t, (nat -> { t' : term & s --> t' }) -> s --> t
where "s --> t" := (sequence s t).

Implicit Arguments Cons [s t u].

(*
   TODO: the induction principle for sequence misses the IH for
   the Lim case. This happened after introducing the sigma type.

   See also
   http://logical.saclay.inria.fr/coq-puma/messages/82e859ccb67f9ab9
   http://pauillac.inria.fr/cdrom_a_graver/www/coq/mailing-lists/coqclub/0402.html
*)

Fixpoint length t s (r : t --> s) : ord' :=
  match r with
  | Nil _          => Zero
  | Cons _ _ r _ _ => Succ (length r)
  | Lim _ _ f      => Limit (fun n => length (projT2 (f n)))
  end.

Fixpoint pref_type t s (r : t --> s) : Type :=
  match r with
  | Nil _          => False
  | Cons _ _ r _ _ => (unit + pref_type r) % type
  | Lim _ _ f      => { n : nat & pref_type (projT2 (f n)) }
  end.

Fixpoint pref t s (r : t --> s) : pref_type r -> { s' : term & t --> s' } :=
  match r in t --> s return pref_type r -> { s' : term & t --> s' } with
  | Nil _           => False_rect _
  | Cons t s' q _ _ => fun i => match i with
                                | inl tt => existT (fun u => t --> u) s' q
                                | inr t  => pref q t
                                end
  | Lim _ _ f       => fun i => match i with
                                | existT n t => pref (projT2 (f n)) t
                                end
  end.

(* Strict prefix relation *)
Inductive prefix : forall `(r : s --> t, q : s --> u), Prop :=
  Pref : forall `(r : s --> t) i, prefix (projT2 (pref r i)) r.

(*
   'Good' sequences have limit functions f where:

     1) n < m implies that (f n) is a prefix of (f m)
     2) for any n, the limit term is equal up to depth n to the end term of some (f m)

   This would be weak convergence.

   => Actually, part 2) does not seem strong enough, it should say that for increasing
      n, m is also increasing...
*)
Fixpoint good s t (r : s --> t) : Prop :=
  match r with
  | Nil _          => True
  | Cons _ _ q _ _ => good q
  | Lim _ t f      => forall n,
                        good (projT2 (f n)) /\
                        (forall m, (n < m)%nat -> prefix (projT2 (f n)) (projT2 (f m))) /\
                        exists m, term_eq_up_to n (projT1 (f m)) t
  end.

(* Length <=, should be equivalent to ord_le *)
Inductive length_le : forall `(r : s --> t, q : u --> v), Prop :=
  | Prefix_Nil  : forall s `(q : u --> v),
                    Nil s <= q
  | Prefix_Cons : forall `(r : s --> t, q : u --> v, p : t [>] w) i,
                    r <= projT2 (pref q i) ->
                    Cons r p <= q
  | Prefix_Lim  : forall `(f : (nat -> { t' : term & s --> t' }), q : u --> v) t,
                    (forall n, projT2 (f n) <= q) ->
                    Lim t f <= q
where "r <= q" := (length_le r q).

(* TODO: can we strengthen this lemma to a < instead of <= ? *)
Lemma prefix_length_le :
  forall `(r : s --> t, q : s --> u),
    prefix r q ->
    r <= q.
Proof.
intros.
destruct H as [s t r i].
induction r as [s | s t r IH u p | s t f].
elim i.
assert (H : projT2 (pref (Cons r p) i) <= r).
destruct i as [[] | i].
simpl.
admit. (* by reflexivity of <= *)
apply IH.
admit. (* by ord_le_succ_right equivalent of <= *)
assert (IH : forall (n : nat) (i : pref_type (projT2 (f n))), projT2 (pref (projT2 (f n)) i) <= projT2 (f n)).
admit. (* missing IH! *)
destruct i as [n i].
assert (H : projT2 (pref (projT2 (f n)) i) <= projT2 (f n)).
apply IH.
admit. (* by ord_le_limit_right equivalent of <= *)
Qed.

(* Another try *)
(*
Inductive prefix : forall s t u, (s --> t) -> (s --> u) -> Prop :=
  | PrefNil  : forall `{r : s --> t}, prefix r r
  | PrefCons : forall `{r : s --> t, q : s --> v, p : v [>] u}, prefix r q -> prefix r (Cons q p)
  | PrefLim  : forall `{r : s --> t, q : s --> v, p : nat -> term, f : (forall n : nat, s --> p n), u},
                 (exists n, p n = v /\ f n = q) -> prefix r q -> prefix r (Lim p f u).
*)

Definition Omega := Limit (fun n => n).

(*
Lemma compression :
  trs_left_linear system ->
  forall r : s --> t,
    strongly_convergent r ->
    exists r' : s --> t,
      strongly_convergent r' /\
      length r' <= Omega.
*)

End TRS.
