Require Export Vector.
Require Export Signature.
Require Export Variables.
Require Import Finite_term.

Set Implicit Arguments.

Section Terms.

Variable F : Signature.
Variable X : Variables.

(* infinite terms *)
CoInductive term : Type :=
  | Var : X -> term
  | Fun : forall f : F, vector term (arity f) -> term.

Notation terms := (vector term).
Notation fterm := (finite_term F X).
Notation fterms := (vector fterm).

Definition root (t : term) : X + F := 
  match t with 
  | Var x   => inl F x
  | Fun f v => inr X f
  end.

(* Trivial image of finite_term in term *)
Fixpoint finite_term_as_term (t : fterm) : term :=
  match t with
  | FVar x      => Var x
  | FFun f args => Fun f (vmap finite_term_as_term args)
  end.

End Terms.

Coercion finite_term_as_term : finite_term >-> term.

Implicit Arguments Var [F X].
