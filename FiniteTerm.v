Require Import Prelims.
Require Import Max. (* TODO: deprecated in Coq 8.3? Max.v -> Peano.v *)
Require Import List.
Require Export Signature.
Require Export Variables.
Require Export Bvector.


Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

Set Implicit Arguments.


Section FiniteTerm.

Variable F : signature.
Variable X : variables.

(* Finitary term datatype *)
Inductive finite_term : Type :=
  | FVar : X -> finite_term
  | FFun : forall f : F, vector finite_term (arity f) -> finite_term.

Reset finite_term_rect.

Notation fterm := (finite_term).
Notation fterms := (vector fterm).

Section InductionPrinciple.

Variables
  (P : fterm -> Type)
  (Q : forall n, fterms n -> Type).

Hypotheses
  (H1 : forall x, P (FVar x))
  (H2 : forall f v, Q v -> P (FFun f v))
  (H3 : Q Vnil)
  (H4 : forall t n (v : fterms n), P t -> Q v -> Q (Vcons t v)).

Fixpoint finite_term_rect t : P t :=
  match t as t return P t with
    | FVar x => H1 x
    | FFun f v =>
      let fix finite_terms_rect n (v : fterms n) {struct v} : Q v :=
        match v as v return Q v with
          | Vnil => H3
          | Vcons t' n' v' => H4 (finite_term_rect t') (finite_terms_rect n' v')
        end
    in H2 f (finite_terms_rect (arity f) v)
  end.

End InductionPrinciple.

Definition finite_term_ind (P : fterm -> Prop) (Q : forall n, fterms n -> Prop) :=
  finite_term_rect P Q.

(* TODO: Bool or prop? *)
Definition is_var (t : fterm) : bool :=
  match t with
  | FVar _ => true
  | _      => false
  end.

Fixpoint size (t : fterm) : nat :=
  match t with
  | FVar _      => 1
  | FFun _ args => 1 + Vfold_right plus (Vmap size args) 0
                    (* vfold 0 (plus * size) args *)
  end.

Fixpoint pattern_depth (t : fterm) : nat :=
  match t with
  | FVar _      => 0
  | FFun _ args => 1 + Vfold_right max (Vmap pattern_depth args) 0
  end.

(* List of variable occurrences in a finite term *)
Fixpoint vars (t : fterm) : list X :=
  match t with
  | FVar x      => x :: nil
  | FFun _ args => Vfold_right (@app X) (Vmap vars args) nil
  end.

(* A finite term is linear if it has no duplicate variable occurrences *)
Definition linear (t : fterm) : Prop :=
  NoDup (vars t).

End FiniteTerm.


Implicit Arguments FVar [F X].
