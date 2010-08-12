(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines substition of terms for variables in terms. *)


Require Export List.
Require Export FiniteTerm.
Require Export Term.
Require Import TermEquality.
Require Import Equality.


Set Implicit Arguments.


Section Substitution.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation fterm := (finite_term F X).

(** A substitution is a function from variables to terms. *)
Definition substitution := X -> term.

(** Equality of substitutions on a list of variables. *)
Fixpoint substitution_eq (vars : list X) (sigma sigma' : substitution) :=
  match vars with
  | nil     => True
  | x :: xs => (substitution_eq xs sigma sigma') /\ (sigma x = sigma' x)
  end.

(** Equality of substitutions on a list of variables is invariant under
   list inclusion.

   We have not yet proven this lemma. This taints the lemma [step_eq__target]
   in [Rewriting]. *)
Lemma substitution_eq_incl :
  forall sigma theta l l',
    incl l' l ->
    substitution_eq l sigma theta ->
    substitution_eq l' sigma theta.
Proof.
intros sigma theta l l' H1 H2.
revert l' H1.
induction l as [| x l IH]; intros l' H1; simpl.
destruct l' as [| y l'].
exact I.
elim (H1 y).
left; reflexivity.

induction l' as [| y l' IH']; simpl.
exact I.
split.
apply IH'.
intros z H.
apply H1.
right.
assumption.
destruct (H1 y).
left; reflexivity.
rewrite H in H2.
apply H2.
simpl in H2.
(** This should not be too hard. (Problem is whether [x] is in [l']. *)
Admitted.

Lemma substitution_eq_app_left :
  forall sigma theta l l',
    substitution_eq (l ++ l') sigma theta ->
    substitution_eq l sigma theta.
Proof.
intros sigma theta l l' H.
induction l as [| x l IH]; simpl.
exact I.
split.
apply IH.
apply H.
apply H.
Qed.

Lemma substitution_eq_app_right :
  forall sigma theta l l',
    substitution_eq (l ++ l') sigma theta ->
    substitution_eq l' sigma theta.
Proof.
intros sigma theta l l' H.
induction l as [| x l IH]; simpl.
assumption.
apply IH.
apply H.
Qed.

Implicit Arguments substitution_eq_app_left [l l'].
Implicit Arguments substitution_eq_app_right [l l'].

(** We show [substitution_eq] is an equivalence. *)

Lemma substitution_eq_refl :
  forall vars sigma, substitution_eq vars sigma sigma.
Proof.
induction vars; [simpl | split]; trivial.
Qed.

Lemma substitution_eq_symm :
  forall vars sigma theta,
    substitution_eq vars sigma theta ->
    substitution_eq vars theta sigma.
Proof.
intros vars sigma theta H.
induction vars as [| x vars IH]; simpl.
exact I.
split.
apply IH.
apply H.
symmetry.
apply H.
Qed.

Lemma substitution_eq_trans :
  forall vars sigma theta upsilon,
    substitution_eq vars sigma theta ->
    substitution_eq vars theta upsilon ->
    substitution_eq vars sigma upsilon.
Proof.
intros vars sigma theta upsilon H1 H2.
induction vars as [| x vars IH]; simpl.
exact I.
split.
apply IH.
apply H1.
apply H2.
apply eq_trans with (theta x).
apply H1.
apply H2.
Qed.

(** The identity substitution. *)
Definition empty_substitution (x : X) : term := Var x.

(** We define two substitution functions. The first, [substitute], defines
   substitution on finite terms. The second, [substitute'], defines
   substitution on infinite terms.

   In principle, [substitute'] works fine and is a generalisation of
   [substitute]. However, it yields a (potentially) infinite term (of type
   [term] instead of [finite_term]) and this makes it somewhat painful to
   work with (corecursive definitions have to be manually unfolded in Coq).

   Since we almost always apply substitutions on finite terms, we define
   this seperately and provide the more general [substitute'] for
   completeness. *)

(** Apply a substitution to a finite term. *)
Fixpoint substitute (sigma : substitution) (t : fterm) {struct t} : term :=
  match t with
  | FVar x      => sigma x
  | FFun f args => Fun f (vmap (substitute sigma) args)
  end.

(** Applying the empty substitution to a finite term gives the trivial
   infinite term image. The only reason we cannot prove coq-equality here
   is equality on vectors. *)
Lemma empty_substitution_is_id :
  forall (t : fterm), substitute empty_substitution t [~] t.
Proof.
induction t.
apply term_bis_refl.
constructor.
assumption.
Qed.

(** Applying equal substitutions yields equal terms.

   We have not yet proven this lemma. This taints the lemmas
   [step_eq_source] and [step_eq_target] in [Rewriting]. *)
Lemma substitution_eq_substitute :
  forall sigma theta t,
    substitution_eq (vars t) sigma theta ->
    substitute sigma t [~] substitute theta t.
Proof.
intros sigma theta t H.
induction t as [x | f args IH]; simpl.
rewrite (proj2 H).
apply term_bis_refl.
constructor.
intro i.
apply IH; clear IH.
simpl in H.
unfold vmap in H.
induction (arity f) as [| n IH]; clear f.
inversion i.
dependent destruction i.
simpl in H.
unfold vhead in H.
unfold vtail in H.
apply (substitution_eq_app_left sigma theta H).
specialize IH with (vtail args) i.
apply IH.
unfold vtail.
(** Here we are stuck, need some more lemmas on [vector], for example:

[[
Lemma a :
  forall x n v,
    In x (vfold nil app (fun i0 : Fin n => vars (v (Next i0)))) ->
    In x (vfold nil app (fun i : Fin (S n) => vars (v i))).
]]
*)
Admitted.

(** Apply a substitution to an infinite term. Note that this definition is
   not in guarded form if we were to use the inductive vector type from the
   standard library. It is in guarded form here, because we use [vector]
   from the [Vector] library, where [vmap] is just an abstraction (which
   ensures the corecursive call to [substitute'] to be guarded). *)
CoFixpoint substitute' (sigma : substitution) (t : term) : term :=
  match t with
  | Var x      => sigma x
  | Fun f args => Fun f (vmap (substitute' sigma) args)
  end.

(** Applying the empty substitution to a term gives the same term. *)
Lemma empty_substitution_is_id' :
  forall (t : term), substitute' empty_substitution t [~] t.
Proof.
cofix IH.
destruct t.
rewrite (peek_eq (substitute' empty_substitution (Var v))).
apply term_bis_refl.
rewrite (peek_eq (substitute' empty_substitution (Fun f v))).
simpl.
constructor.
intro i.
unfold vmap.
apply IH.
Qed.

(** We prove that both substitution functions do the same thing (on finite
   terms). We can almost prove this for coq-equality, but we cannot equate
   [vmap finite_term_as_term v] and [v]. *)
Lemma substitutions_related :
  forall (s : substitution) (t : fterm), substitute s t [~] substitute' s t.
Proof.
induction t.
simpl.
rewrite (peek_eq (substitute' s (Var v))).
simpl.
destruct (s v); apply term_bis_refl.
simpl.
rewrite (peek_eq (substitute' s (Fun f (vmap (@finite_term_as_term F X) v)))).
simpl.
constructor.
intro i.
unfold vmap.
apply H.
Qed.

End Substitution.
