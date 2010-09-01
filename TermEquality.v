(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                     Dimitri Hendriks <diem@cs.vu.nl>                 *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines two equalities on infinite terms:
    - Bisimilarity by [term_bis]
    - Pointwise equality by [term_eq]

    These two relations are proved to be the same and to be equivalences.

    In the last section, a third equality via positions is introduced,
    but it is not yet proven equal to the first two. *)


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

(** Bisimilarity on terms. *)
CoInductive term_bis : term -> term -> Prop :=
  | Var_bis : forall x, term_bis (Var x) (Var x)
  | Fun_bis : forall f v w,
              (forall i, term_bis (v i) (w i)) ->
              term_bis (Fun f v) (Fun f w).

(** Equality of infinite terms up to a given depth. *)
Inductive term_eq_up_to : nat -> term -> term -> Prop :=
  | teut_0   : forall t u, term_eq_up_to 0 t u
  | teut_var : forall d x, term_eq_up_to d (Var x) (Var x)
  | teut_fun : forall d f v w,
               (forall i, term_eq_up_to d (v i) (w i)) ->
               term_eq_up_to (S d) (Fun f v) (Fun f w).

(** Pointwise equality by generalising equality up to a given depth. *)
Definition term_eq (t u : term) :=
  forall d, term_eq_up_to d t u.

(** Some inversion lemmas on pointwise equality. *)

Lemma teut_fun_inv :
  forall d f v w,
  term_eq_up_to (S d) (Fun f v) (Fun f w) ->
  forall i, term_eq_up_to d (v i) (w i).
Proof.
intros d f v w H.
dependent destruction H.
assumption.
Qed.

Lemma term_eq_fun_inv :
  forall f v w,
  term_eq (Fun f v) (Fun f w) ->
  forall i, term_eq (v i) (w i).
Proof.
intros f v w H i n.
apply teut_fun_inv with (1 := H (S n)).
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

(** We now prove that bisimilarity is the same as pointwise equality. *)

(** Bisimilarity implies pointwise equality. *)
Lemma term_bis_implies_term_eq :
  forall (t u : term), term_bis t u -> term_eq t u.
Proof.
intros t u H d.
generalize t u H; clear H t u.
induction d as [| d IHd]; intros t u H.
constructor.
destruct H.
constructor.
constructor.
intro i.
apply IHd with (1:=(H i)).
Qed.

(** Pointwise equality implies bisimilarity. *)
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
intro i.
assert (H0 := term_eq_fun_inv H).
apply eq2bis.
apply H0.
Qed.

Lemma term_bis_term_eq :
  forall (t u : term), term_bis t u <-> term_eq t u.
Proof.
split.
apply term_bis_implies_term_eq.
apply term_eq_implies_term_bis.
Qed.

(** Pointwise equality is an equivalence. *)

Lemma term_eq_up_to_trans :
  forall d t u v,
    term_eq_up_to d t u ->
    term_eq_up_to d u v ->
    term_eq_up_to d t v.
Proof.
induction d as [| d IH].
constructor.
intros t u v H1.
inversion_clear H1; intro H2.
assumption.
dependent destruction H2.
constructor.
intro i.
apply IH with (u := w i); trivial.
Qed.

Lemma term_eq_up_to_refl :
  forall d t,
    term_eq_up_to d t t.
Proof.
induction d as [| d IH]; intro t.
constructor.
destruct t.
constructor.
constructor.
intro.
apply IH.
Qed.

Lemma term_eq_up_to_symm :
  forall d t u,
    term_eq_up_to d t u ->
    term_eq_up_to d u t.
Proof.
induction d as [| d IH]; intros t u H.
constructor.
inversion_clear H.
constructor.
constructor.
intro.
apply IH.
apply H0.
Qed.

Lemma term_eq_refl : forall t, term_eq t t.
Proof.
intros t d.
apply (term_eq_up_to_refl d t).
Qed.

Lemma term_eq_symm :
  forall t u, term_eq t u -> term_eq u t.
Proof.
intros t u H d.
apply (term_eq_up_to_symm (H d)).
Qed.

Lemma term_eq_trans :
  forall t u v, term_eq t u -> term_eq u v -> term_eq t v.
Proof.
intros t u v H1 H2 d.
apply (term_eq_up_to_trans (H1 d) (H2 d)).
Qed.

(** Bisimilarity is an equivalence. *)

Lemma term_bis_refl :
  forall t, term_bis t t.
Proof.
cofix.
destruct t as [x|f v]; constructor.
intro i.
apply term_bis_refl.
Qed.

Lemma term_bis_symm :
  forall t u, term_bis t u -> term_bis u t.
Proof.
cofix.
destruct 1 as [x|f v w H]; constructor.
intro i.
apply term_bis_symm.
apply H.
Qed.

Lemma term_bis_trans :
  forall s t u, term_bis s t -> term_bis t u -> term_bis s u.
Proof.
cofix.
destruct 1 as [x|f xs ys H1].
intro. assumption.
intro H2.
dependent destruction H2.
rename w into zs, H into H2.
constructor; intro i.
apply term_bis_trans with (1:=(H1 i)) (2:=(H2 i)).
Qed.

(** Two weakening lemmas on pointwise equality follow. *)

Lemma term_eq_up_to_weaken :
  forall t u d, term_eq_up_to (S d) t u -> term_eq_up_to d t u.
Proof.
intros t u d H.
revert t u H.
induction d; intros t u H.
constructor.
inversion_clear H.
apply term_eq_up_to_refl.
constructor.
intro i.
apply IHd.
apply H0.
Qed.

Lemma term_eq_up_to_weaken_generalized :
  forall t u n m,
    n <= m ->
    term_eq_up_to m t u ->
    term_eq_up_to n t u.
Proof.
induction 1 as [| m H IH]; intro.
assumption.
apply IH.
apply term_eq_up_to_weaken.
assumption.
Qed.

(** Cauchy-converence for a sequence of terms. This is used in the definition
   of rewrite sequences in the library [Rewriting]. *)
Definition converges (f : nat -> term) (t : term) : Prop :=
  forall d, exists n, forall m,
    n <= m ->
    term_eq_up_to d (f m) t.

End TermEquality.


Infix " [~] " := term_bis (no associativity, at level 70).
Infix " [=] " := term_eq (no associativity, at level 70).


Section PositionEquality.

(** We introduce a third equality via positions, but we did not yet succeed
   at proving it equal to the first two. *)

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation terms := (vector term).

(** Equality of terms at a given position. *)
Definition pos_eq (p : position) (t u : term) :=
  match subterm t p, subterm u p with
  | None,   None   => True
  | Some t, Some u => root t = root u
  | _,      _      => False
  end.

(** Equality of terms at all positions. *)
Definition all_pos_eq (t u : term) :=
  forall p : position, pos_eq p t u.

(**
   Didn't really bother to complete this...

[[
Lemma all_pos_eq_fun_inv :
  forall f v w,
    all_pos_eq (Fun f v) (Fun f w) ->
    forall i, all_pos_eq (v i) (w i).
Proof.
intros f v w H i.
revert v w H.
dependent destruction i; intros v w H1 p.
assert (H' := H1 (0 :: p)).
unfold pos_eq in H'.
unfold subterm in H'.
destruct (Bool_nat.lt_ge_dec 0 (arity f)).
unfold pos_eq.
unfold subterm.
assert (vnth_fact : vnth l v = v i0 /\ vnth l w = w i0).
admit. (** vnth should do this *)
rewrite (proj1 vnth_fact), (proj2 vnth_fact) in H'.
assumption.
assert (Habsurd : arity f = 0).
auto with arith.
rewrite Habsurd in *|-.
(** The ugly thing is that dependent destruction i uses different names x0
   (Coq 8.3) and H (Coq 8.2). *)
discriminate.
(** I don't know if we're on the right track here. *)
]]

[[
Lemma all_pos_eq_implies_term_bis :
  forall (t u : term), all_pos_eq t u -> t [~] u.
Proof.
cofix pos2bis.
intros t u H.
assert (H1 := H nil).
unfold pos_eq in H1.
unfold subterm in H1.
destruct t; destruct u. (* "destruct t, u." syntax is Coq 8.3 only *)
injection H1; intro e; rewrite e; apply term_bis_refl.
discriminate H1.
discriminate H1.
dependent destruction H1. (* injection H1; clear H1; intro e; rewrite e. *)
constructor.
intro i.
apply pos2bis.
apply (all_pos_eq_fun_inv H).
Qed.
]]

[[
Lemma term_bis_implies_all_pos_eq :
  forall (t u : term), t [~] u -> all_pos_eq t u.
Proof.
intros t u H p.
revert t u H.
induction p as [| a p IH]; intros t u [x | f v w H].
reflexivity.
reflexivity.
exact I.
unfold pos_eq; simpl; destruct (Bool_nat.lt_ge_dec a (arity f)).
(** vnth should do this of course *)
assert (vnth_fact : exists i : Fin (arity f), vnth l v = v i /\ vnth l w = w i).
admit.
destruct vnth_fact as [i [H1 H2]].
rewrite H1, H2.
assert (Hp := IH (v i) (w i) (H i)).
unfold pos_eq in Hp.
destruct (subterm (v i) p); destruct (subterm (w i) p); assumption.
exact I.
Qed.
]]
*)

End PositionEquality.
