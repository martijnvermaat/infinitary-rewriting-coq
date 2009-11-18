Require Export Finite_term.
Require Export Term.
(*Require Import Term_equality.*)

Set Implicit Arguments.

Section Substitution.

Variable F : Signature.

Notation term := (term F).
Notation fterm := (finite_term F).

(* Type of substitutions of terms for variables *)
Definition substitution := variable -> term.

(* The identity substitution *)
Definition empty_substitution (x : variable) : term := Var x.

(* Apply a substitution to a finite term *)
Fixpoint substitute (sigma : substitution) (t : fterm) {struct t} : term :=
  match t with
  | FVar x      => sigma x
  | FFun f args => Fun f (vmap (substitute sigma) args)
  end.

(* DH bezig hier ... *)
(*
(* Applying the empty substitution to a finite term gives the trivial infinite term image *)
Lemma empty_substitution_is_trivial :
  forall (t : finite_term), substitute empty_substitution t == finite_term_as_term t.
Proof.
  induction t as [x|f v]; simpl.
	(* t = FVar x *)
	apply empty_substitution_is_id.
	(* t = FFun f subterms *)
	(* TODO: Induction principle is probably no good (see ATerm.v in CoLoR) *)
Abort.
*)

End Substitution.
