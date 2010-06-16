Require Export List.
Require Import Bool_nat.
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

(*
   TODO: I don't think this is a usefull definition, we probably can never
   prove a term to be infinite?
   I guess we could use bisimilarity instead of Coq convertibility.
*)
(*
Definition infinite (t : term) : Prop :=
  exists t' : fterm, finite_term_as_term t' [=] t.
*)

End Term.


Notation position := (list nat).


Section Position.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).

Definition position_depth (p : position) := length p.

(* Subterm at position *)
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

(*
   TODO: maybe we should build in inductive Finite and/or coinductive
   Infinite property (as in A Tutorial on (Co)Inductive Types)
*)
Definition infinite (t : term) : Prop :=
  forall d,
    exists p : position,
      position_depth p = d /\ subterm t p <> None.

End Position.


Implicit Arguments Var [F X].


Coercion finite_term_as_term : finite_term >-> term.
