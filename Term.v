Require Import Prelims.
Require Export List.
Require Export Bvector.
Require Export Signature.
Require Export Variables.
Require Import FiniteTerm.


Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

Set Implicit Arguments.


Notation position := (list nat).


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
  | Var x   => inl x
  | Fun f v => inr f
  end.

Require Import Bool_nat.

(* Subterm at position *)
Fixpoint subterm (t : term) (p : position) {struct p} : option term :=
  match p with
  | nil    => Some t
  | n :: p => match t with
              | Var _      => None
              | Fun f args => match lt_ge_dec n (arity f) with
                              | left h  => subterm (Vnth args h) p
                              | right _ => None
                              end
              end
  end.

(* Trivial image of finite_term in term *)
Fixpoint finite_term_as_term (t : fterm) : term :=
  match t with
  | FVar x      => Var x
  | FFun f args => Fun f (Vmap finite_term_as_term args)
  end.

(*
   TODO: I don't think this is a usefull definition, we probably can never
   prove a term to be infinite?
   I guess we could use bisimilarity instead of Coq convertibility.
*)
Definition finite (t : term) : Prop :=
  exists t' : fterm, finite_term_as_term t' = t.

End Term.


Implicit Arguments Var [F X].

Coercion finite_term_as_term : finite_term >-> term.
