Require Export List.
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

(* Equality of substitutions on a list of variables *)
Fixpoint substitution_eq (vars : list X) (sigma sigma' : substitution) :=
  match vars with
  | nil     => True
  | x :: xs => (substitution_eq xs sigma sigma') /\ (sigma x = sigma' x)
  end.

(* This equality is reflexive *)
Lemma substitution_eq_refl :
  forall vars sigma, substitution_eq vars sigma sigma.
Proof.
induction vars; [simpl | split]; trivial.
Qed.

(* The identity substitution *)
Definition empty_substitution (x : X) : term := Var x.

(* Apply a substitution to a finite term *)
Fixpoint substitute (sigma : substitution) (t : fterm) {struct t} : term :=
  match t with
  | FVar x      => sigma x
  | FFun f args => Fun f (vmap (substitute sigma) args)
  end.

(* Applying the empty substitution to a finite term gives the trivial infinite term image *)
(* The only reason we cannot prove coq-equality here is equality on vectors *)
Lemma empty_substitution_is_trivial :
  forall (t : fterm), substitute empty_substitution t [~] t.
Proof.
induction t.
apply term_bis_refl.
constructor.
assumption.
Qed.

(* TODO: with the recursive vectors we can also define this as a cofixpoint on
   (non-finite) terms. Below are some additional lemmas for reassurance. *)
CoFixpoint substitute' (sigma : substitution) (t : term) : term :=
  match t with
  | Var x      => sigma x
  | Fun f args => Fun f (vmap (substitute' sigma) args)
  end.

(* Take apart a coinductive term up to depth 1 and put it back together *)
(* TODO: move to Term.v *)
Definition peek (t : term) : term :=
  match t with
  | Var x      => Var x
  | Fun f args => Fun f args
  end.

Lemma peek_eq : forall (t : term), t = peek t.
  destruct t; reflexivity.
Qed.

(* Applying the empty substitution to a finite term gives the trivial infinite term image *)
Lemma empty_substitution_is_trivial' :
  forall (t : term), substitute' empty_substitution t [~] t.
Proof.
cofix IH.
destruct t.
rewrite (peek_eq (substitute' empty_substitution (Var v))).
apply term_bis_refl.
rewrite (peek_eq (substitute' empty_substitution (Fun f v))).
simpl.
constructor.
intro i.
unfold vmap.
apply IH.
Qed.

(* the following can be proved for coq-equality were it not that
   we cannot equate (vmap finite_term_as_term v) and v *)
Lemma substitutions_related :
  forall (s : substitution) (t : fterm), substitute s t [~] substitute' s t.
Proof.
induction t.
simpl.
rewrite (peek_eq (substitute' s (Var v))).
simpl.
destruct (s v); apply term_bis_refl.
simpl.
rewrite (peek_eq (substitute' s (Fun f (vmap (@finite_term_as_term F X) v)))).
simpl.
constructor.
intro i.
unfold vmap.
apply H.
Qed.

End Substitution.
