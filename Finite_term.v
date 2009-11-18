Require Import List.
Require Import Signature.
Require Import Variables.
Require Export Vector.

Set Implicit Arguments.

Section Finite_terms.

Variable F : Signature.
Variable X : Variables.

(* Finitary term datatype *)
Inductive finite_term : Type :=
  | FVar : X -> finite_term
  | FFun : forall f : F, vector finite_term (arity f) -> finite_term.

Notation fterm := (finite_term).
Notation fterms := (vector fterm).

Definition is_var (t : fterm) : bool :=
  match t with 
  | FVar _ => true
  | _      => false
  end.

Fixpoint size (t : fterm) : nat :=
  match t with
  | FVar _      => 1
  | FFun _ args => 1 + vfold 0 plus (vmap size args) 
                    (* vfold 0 (plus * size) args *)
  end.

(* List of variable occurrences in a finite term *)

Fixpoint vars (t : fterm) : list X :=
  match t with
  | FVar x      => x :: nil
  | FFun _ args => vfold nil (@app X) (vmap vars args)
  end.

(* A finite term is linear if it has no duplicate variable occurrences *)
Definition linear (t : fterm) : Prop :=
  NoDup (vars t).

End Finite_terms.