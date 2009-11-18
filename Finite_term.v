Require Import List.
Require Export Signature.
Require Export Vector.

Set Implicit Arguments.

Section Finite_terms.

Variable F : Signature.

(* Finitary term datatype *)
Inductive finite_term : Type :=
  | FVar : variable -> finite_term
  | FFun : forall f : F, vector finite_term (arity f) -> finite_term.

Notation fterm := (finite_term).
Notation fterms := (vector fterm).

(* NOTE: Why bool? We want to use it in formulas *)
Definition is_var (t : fterm) : Prop :=
  match t with
  | FVar _ => True
  | _      => False
  end.

Fixpoint size (t : fterm) : nat :=
  match t with
  | FVar _      => 1
  | FFun _ args => 1 + vfold 0 plus (vmap size args)
                    (* vfold 0 (plus * size) args *)
  end.

(* List of variable occurrences in a finite term *)

Fixpoint vars (t : fterm) : list variable :=
  match t with
  | FVar x      => x :: nil
  | FFun _ args => vfold nil (@app variable) (vmap vars args)
  end.

(* A finite term is linear if it has no duplicate variable occurrences *)
Definition linear (t : fterm) : Prop :=
  NoDup (vars t).

End Finite_terms.
