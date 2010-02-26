Require Export Vector.
Require Export Signature.
Require Export Variables.
Require Import FiniteTerm.


Set Implicit Arguments.


Section Term.

Variable F : signature.
Variable X : variables.

(* Infinite terms *)
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

(* Trivial image of finite_term in term *)
Fixpoint finite_term_as_term (t : fterm) : term :=
  match t with
  | FVar x      => Var x
  | FFun f args => Fun f (vmap finite_term_as_term args)
  end.

End Term.


Implicit Arguments Var [F X].

Coercion finite_term_as_term : finite_term >-> term.
