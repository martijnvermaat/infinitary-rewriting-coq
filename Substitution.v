Require Export FiniteTerm.
Require Export Term.
Require Import TermEquality.


Set Implicit Arguments.


Section Substitution.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation fterm := (finite_term F X).

(* Type of substitutions of terms for variables *)
Definition substitution := X -> term.

(* The identity substitution *)
Definition empty_substitution (x : X) : term := Var x.

(* Apply a substitution to a finite term *)
Fixpoint substitute (sigma : substitution) (t : fterm) {struct t} : term :=
  match t with
  | FVar x      => sigma x
  | FFun f args => Fun f (vmap (substitute sigma) args)
  end.

(* Applying the empty substitution to a finite term gives the trivial infinite term image *)
Lemma empty_substitution_is_trivial :
  forall (t : fterm), substitute empty_substitution t [~] t.
Proof.
induction t.
apply term_bis_refl.
constructor.
assumption.
Qed.

End Substitution.
