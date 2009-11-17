Require Import List.
Require Import Signature.
Require Import Variables.



Set Implicit Arguments.

Section Finite_terms.

Variable F : Signature.
Variable X : Variables.

(* Finitary term datatype *)
Inductive finite_term : Type :=
  | FVar : X -> finite_term
  | FFun : forall f : F, vector finite_term (arity f) -> finite_term.

Reset finite_term_rect.

Notation fterm := (finite_term).
Notation fterms := (vector fterm).

Section finite_term_rect. 
(* copied from CoLoR/Term/WithArity/ATerm.v *)

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

End finite_term_rect.

Definition finite_term_ind (P : fterm -> Prop) (Q : forall n, fterms n -> Prop) :=
  finite_term_rect P Q.

Definition is_var (t : fterm) : bool :=
  match t with 
  | FVar _ => true
  | _      => false
  end.

(* List of variable occurrences in a finite term *)
Fixpoint vars (t : fterm) : list X :=
  match t with
  | FVar x   => x :: nil
  | FFun f v =>
      let fix vars_vec n (v : fterms n) {struct v} : list X :=
        match v with
	  | Vnil         => nil
	  | Vcons u m us => vars u ++ vars_vec m us
	end
      in vars_vec (arity f) v
  end.

(* A finite term is linear if it has no duplicate variable occurrences *)
Definition linear (t : fterm) : Prop :=
  NoDup (vars t).

End Finite_terms.