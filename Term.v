(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines the type [term] of infinite terms. *)


Require Export List.
Require Import Bool_nat.
Require Export Vector.
Require Export Signature.
Require Export Variables.
Require Import FiniteTerm.


Set Implicit Arguments.


Section Term.

(** Terms are defined coinductively over a signature [F] and a set of
   variables [X]. *)

Variable F : signature.
Variable X : variables.

CoInductive term : Type :=
  | Var : X -> term
  | Fun : forall f : F, vector term (arity f) -> term.

Notation terms := (vector term).
Notation fterm := (finite_term F X).
Notation fterms := (vector fterm).

Definition root (t : term) : X + F :=
  match t with
  | Var x   => inl _ x
  | Fun f v => inr _ f
  end.

Definition is_var (t : term) : bool :=
  match t with
  | Var _ => true
  | _     => false
  end.

(** Trivial image of [finite_term] in [term]. *)
Fixpoint finite_term_as_term (t : fterm) : term :=
  match t with
  | FVar x      => Var x
  | FFun f args => Fun f (vmap finite_term_as_term args)
  end.

End Term.


Implicit Arguments Var [F X].

Coercion finite_term_as_term : finite_term >-> term.

Notation position := (list nat).


Section Position.

(** Positions in terms are lists of natural numbers. *)

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation fterm := (finite_term F X).

Definition position_depth (p : position) := length p.

(*
   Instead of the definitions with option types, we could also define the
   set of positions for a term and then require 'correct' positions by
   typing.
*)

(** Subterm of a term at some position. *)
Fixpoint subterm (t : term) (p : position) {struct p} : option term :=
  match p with
  | nil    => Some t
  | n :: p => match t with
              | Var _      => None
              | Fun f args => match lt_ge_dec n (arity f) with
                              | left h  => subterm (vnth h args) p
                              | right _ => None
                              end
              end
  end.

(* This is a quick hack so substitutions can work on subterms *)

(** Subterm of a finite term at some position is again finite. *)
Fixpoint finite_subterm (t : fterm) (p : position) {struct p} : option fterm :=
  match p with
  | nil    => Some t
  | n :: p => match t with
              | FVar _      => None
              | FFun f args => match lt_ge_dec n (arity f) with
                               | left h  => finite_subterm (vnth h args) p
                               | right _ => None
                               end
              end
  end.

(* The term_inf predicate is defined as in A Tutorial on (Co)Inductive
   Types. *)

(** Coinductive infinite predicate. *)
CoInductive term_inf : term -> Prop :=
  | Fun_inf : forall f v i, term_inf (v i) -> term_inf (Fun f v).

(** Alternative infinite predicate via positions. *)
Definition infinite (t : term) : Prop :=
  forall d,
    exists p : position,
      position_depth p = d /\ subterm t p <> None.

(** I guess we should be able to prove these predicates to define the same
    subset of infinite terms, but my (small) tries below did not succeed. *)

Require Import Equality.

(* But we cannot prove this *)
Lemma infinite_implies_term_inf :
  forall t, infinite t -> term_inf t.
Proof.
cofix co.
intros [x | f v] H.
unfold infinite in H.
specialize H with 1.
destruct H as [[| a p] [D H]].
inversion D.
contradict H.
reflexivity.
(** We need to establish that there is an n such that
   for every depth there exists a p with n::p etc.

   I don't see how to get there, but it ought to be
   possible since (arity f) is finite, using something
   akin to the pigeon hole principle. *)
Admitted.

Lemma term_inf_implies_infinite :
  forall t, term_inf t -> infinite t.
Proof.
intros t H d.
revert t H.
induction d as [| d IH]; intros t H.
exists nil.
split.
reflexivity.
discriminate.
destruct H.
specialize IH with (v i).
destruct IH as [p [D IH]].
assumption.
(* Seems like we need some way of getting an n from an i *)
revert IH.
dependent induction i.
intro IH.
exists (0 :: p).
split.
simpl.
reflexivity.
simpl.
destruct (arity f).
inversion i0.
simpl.
unfold vhead.
admit. (* Don't know what to do here *)
intro IH.
(** And we are stuck. *)
Admitted.

End Position.
