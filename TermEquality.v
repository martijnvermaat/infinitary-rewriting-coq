Require Import Prelims.
Require Import Signature.
Require Import Variables.
Require Import Term.
Require Import Equality.


Set Implicit Arguments.


Section TermEquality.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation terms := (vector term).

(* Bisimilarity on terms *)
CoInductive term_bis : term -> term -> Prop :=
  | Var_bis : forall x, term_bis (Var x) (Var x)
  | Fun_bis : forall f v w,
              (forall n (H : n < arity f), term_bis (Vnth v H) (Vnth w H)) ->
              term_bis (Fun f v) (Fun f w).

(*
CoInductive term_bis : term -> term -> Prop :=
  | Var_bis : forall x, term_bis (Var x) (Var x)
  | Fun_bis : forall f v w,
              terms_bis v w ->
              term_bis (Fun f v) (Fun f w)
with terms_bis : forall n, terms n -> terms n -> Prop :=
  | O_bis  : forall (v w : terms 0), terms_bis v w
  | Sn_bis : forall n (v w : terms n) t s,
             terms_bis v w ->
             term_bis t s ->
             terms_bis (Vcons t v) (Vcons s w).
*)

(* Equality of infinite terms up to a given depth *)
Inductive term_eq_up_to : nat -> term -> term -> Prop :=
  | teut_0   : forall t u : term, term_eq_up_to 0 t u
  | teut_var : forall n x, term_eq_up_to n (Var x) (Var x)
  | teut_fun : forall n f v w,
               (forall m (H : m < arity f), term_eq_up_to n (Vnth v H) (Vnth w H)) ->
               term_eq_up_to (S n) (Fun f v) (Fun f w).

Definition term_eq (t u : term) :=
  forall n, term_eq_up_to n t u.

(* We do not see how to prove the following lemma without appeal to JMeq
   (as used by the tactic [dependent destruction]):
*)
Lemma teut_fun_inv :
  forall n f v w,
  term_eq_up_to (S n) (Fun f v) (Fun f w) ->
  forall m (H : m < arity f), term_eq_up_to n (Vnth v H) (Vnth w H).
Proof.
intros n f v w H.
dependent destruction H.
assumption.
Qed.

Lemma term_eq_fun_inv :
  forall f v w,
  term_eq (Fun f v) (Fun f w) ->
  forall n (H : n < arity f), term_eq (Vnth v H) (Vnth w H).
Proof.
intros f v w H m h n.
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
intros m h.
apply IHn with (1:=(H m h)).
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
cofix eq2bis.
intros [x|f v] [y|g w] H.
assert (H0 := H 7); inversion_clear H0.
constructor.
assert (H0 := H 1); inversion_clear H0.
assert (H0 := H 1); inversion_clear H0.
assert (H0 := term_eq_fun_inv_symbol H).
dependent destruction H0.
apply Fun_bis.
intros n h.
assert (H0 := term_eq_fun_inv H).
apply eq2bis.
apply H0.
Qed.

Lemma term_eq_up_to_trans :
  forall n t u v,
    term_eq_up_to n t u ->
    term_eq_up_to n u v ->
    term_eq_up_to n t v.
Proof.
induction n as [| n IH].
constructor.
intros t u v H1.
inversion_clear H1; intro H2.
assumption.
dependent destruction H2.
constructor.
intros m h.
apply IH with (u := Vnth w h); trivial.
Qed.

(* TODO: define term_eq_refl and term_eq_symm using the
   term_eq_up_to_* equivalents, just like the *_trans case. *)
Lemma term_eq_up_to_refl :
  forall n t,
    term_eq_up_to n t t.
Proof.
Admitted.

Lemma term_eq_up_to_symm :
  forall n t u,
    term_eq_up_to n t u ->
    term_eq_up_to n u t.
Proof.
Admitted.

Lemma term_eq_refl : forall t, term_eq t t.
Proof.
intros t n.
revert t.
induction n as [| n IH]; intro t.
constructor.
destruct t.
constructor.
constructor.
intros.
apply IH.
Qed.

Lemma term_eq_symm : forall t u, term_eq t u -> term_eq u t.
Proof.
intros t u H n.
assert (H' := H n). clear H.
revert t u H'.
induction n; intros.
constructor.
inversion_clear H'.
constructor.
constructor.
intros.
apply IHn.
apply H.
Qed.

Lemma term_eq_trans : forall t u v, term_eq t u -> term_eq u v -> term_eq t v.
Proof.
intros t u v H1 H2 n.
apply (term_eq_up_to_trans (H1 n) (H2 n)).
Qed.

Lemma term_bis_refl : forall t, term_bis t t.
cofix.
destruct t as [x|f v]; constructor.
intros n h.
apply term_bis_refl.
Qed.

Lemma term_bis_symm : forall t u, term_bis t u -> term_bis u t.
cofix.
destruct 1 as [x|f v w H]; constructor.
intros n h.
apply term_bis_symm.
apply H.
Qed.

Lemma term_bis_trans : forall s t u, term_bis s t -> term_bis t u -> term_bis s u.
cofix.
destruct 1 as [x|f xs ys H1].
intro. assumption.
intro H2.
(*
generalize H1; clear H1 .
inversion H2 as [|g ys' zs].
*)
dependent destruction H2.
rename w into zs, H into H2.
constructor; intros n h.
apply term_bis_trans with (1:=(H1 n h)) (2:=(H2 n h)).
Qed.

End TermEquality.


Infix " [~] " := term_bis (no associativity, at level 70).
Infix " [=] " := term_eq (no associativity, at level 70).
