(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines the type [finite_term] of finite terms. *)


Require Import Max. (* TODO: deprecated in Coq 8.3? Max.v -> Peano.v *)
Require Import List.
Require Export Signature.
Require Export Variables.
Require Export Vector.


Set Implicit Arguments.


Section FiniteTerm.

(** Terms are defined inductively over a signature [F] and a set of
   variables [X]. *)

Variable F : signature.
Variable X : variables.

Inductive finite_term : Type :=
  | FVar : X -> finite_term
  | FFun : forall f : F, vector finite_term (arity f) -> finite_term.

Notation fterm := (finite_term).
Notation fterms := (vector fterm).

Fixpoint size (t : fterm) : nat :=
  match t with
  | FVar _      => 1
  | FFun _ args => 1 + vfold 0 plus (vmap size args)
                    (* vfold 0 (plus * size) args *)
  end.

Fixpoint pattern_depth (t : fterm) : nat :=
  match t with
  | FVar _      => 0
  | FFun _ args => 1 + vfold 0 max (vmap pattern_depth args)
  end.

(** List of variable occurrences in a finite term. *)
Fixpoint vars (t : fterm) : list X :=
  match t with
  | FVar x      => x :: nil
  | FFun _ args => vfold nil (@app X) (vmap vars args)
  end.

(** A finite term is linear if it has no duplicate variable occurrences. *)
Definition linear (t : fterm) : Prop :=
  NoDup (vars t).

End FiniteTerm.


Implicit Arguments FVar [F X].
