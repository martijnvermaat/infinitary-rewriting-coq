Require Export Vector.
Require Export Signature.
Require Import Finite_term.

Set Implicit Arguments.

Section Terms.

Variable F : Signature.

(* infinite terms *)
CoInductive term : Type :=
  | Var : variable -> term
  | Fun : forall f : F, vector term (arity f) -> term.

Notation terms := (vector term).
Notation fterm := (finite_term F).
Notation fterms := (vector fterm).

(* Trivial image of finite_term in term *)
Fixpoint finite_term_as_term (t : fterm) : term :=
  match t with
  | FVar x      => Var x
  | FFun f args => Fun f (vmap finite_term_as_term args)
  end.

End Terms.

Implicit Arguments Var [F].
