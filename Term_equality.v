Require Import Signature.
Require Import Variables.
Require Import Term.
Require Import Equality.

Set Implicit Arguments.

Section term_equality.

Variable F : Signature.
Variable X : Variables.

Notation term := (term F X).
Notation terms := (vector term).

(* Bisimilarity on terms *)

CoInductive term_bis : term -> term -> Prop :=
  | Var_bis : forall x, term_bis (Var x) (Var x)
  | Fun_bis : forall f v w, 
              (forall i, term_bis (v i) (w i)) -> 
              term_bis (Fun f v) (Fun f w).

(* Equality of infinite terms up to a given depth *)

Inductive term_eq_up_to : nat -> term -> term -> Prop :=
  | teut_0   : forall t u : term, term_eq_up_to 0 t u
  | teut_var : forall n x, term_eq_up_to n (Var x) (Var x)
  | teut_fun : forall n f v w, 
               (forall i, term_eq_up_to n (v i) (w i)) -> 
               term_eq_up_to (S n) (Fun f v) (Fun f w).

Definition term_eq (t u : term) := 
  forall n, term_eq_up_to n t u.

(* We do not see how to prove the following lemma without appeal to JMeq 
   (as used by the tactic [dependent destruction]):
*)

Lemma teut_fun_inv :
  forall n f v w,
  term_eq_up_to (S n) (Fun f v) (Fun f w) ->
  forall i, term_eq_up_to n (v i) (w i).
intros n f v w H.
dependent destruction H.
assumption.
Qed.

Lemma term_eq_fun_inv :
  forall f v w,
  term_eq (Fun f v) (Fun f w) ->
  forall i, term_eq (v i) (w i).
intros f v w H i n.
apply teut_fun_inv with (1 := H (S n)).
Qed.

Lemma term_bis_implies_term_eq : 
  forall (t u : term), term_bis t u -> term_eq t u.
Proof.
intros t u H n.
generalize t u H; clear H t u.
induction n as [| n IHn]; intros t u H.
constructor.
destruct H.
constructor.
constructor.
intro i.
apply IHn with (1:=(H i)).
Qed.

Lemma term_eq_fun_inv_symbol : 
  forall (f g : F) (v : terms (arity f)) (w : terms (arity g)),
  term_eq (Fun f v) (Fun g w) -> f = g.
Proof.
intros f g v w H.
assert (H0 := H 1).
inversion_clear H0; simpl.
reflexivity.
Qed.

Lemma term_eq_implies_term_bis : forall (t u : term), term_eq t u -> term_bis t u.
Proof.
cofix coIH.
intros [x|f v] [y|g w] H.
assert (H0 := H 7); inversion_clear H0.
constructor.
assert (H0 := H 1); inversion_clear H0.
assert (H0 := H 1); inversion_clear H0.
assert (H0 := term_eq_fun_inv_symbol H).
dependent destruction H0.
apply Fun_bis.
intro i.
assert (H0 := term_eq_fun_inv H).
apply coIH.
apply H0.
Qed.

End term_equality.

Infix "[~]" := term_bis (no associativity, at level 70).
Infix "[=]" := term_eq (no associativity, at level 70).