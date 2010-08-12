(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines two equalities on contexts:
    - Bisimilarity by [context_bis]
    - Pointwise equality by [context_eq]

    These two relations are proved to be the same and to be equivalences. *)


Require Import Signature.
Require Import Variables.
Require Import Context.
Require Import Equality.


Set Implicit Arguments.


Section ContextEquality.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation terms := (vector term).
Notation context := (context F X).

(* Bisimilarity on contexts *)
Inductive context_bis : context -> context -> Prop :=
  | Hole_bis : context_bis Hole Hole
  | CFun_bis : forall f i j H H' (v v' : terms i) c c' (w w' : terms j),
               (forall i, term_bis (v i) (v' i)) ->
               context_bis c c' ->
               (forall i, term_bis (w i) (w' i)) ->
               context_bis (CFun f H v c w) (CFun f H' v' c' w').

(* Equality of contexts up to a given depth *)
Inductive context_eq_up_to : nat -> context -> context -> Prop :=
  | ceut_0    : forall c c' : context, context_eq_up_to 0 c c'
  | ceut_hole : forall n, context_eq_up_to n Hole Hole
  | ceut_cfun : forall d f i j H H' (v v' : terms i) c c' (w w' : terms j),
                (forall i, term_eq_up_to d (v i) (v' i)) ->
                context_eq_up_to d c c' ->
                (forall i, term_eq_up_to d (w i) (w' i)) ->
                context_eq_up_to (S d) (CFun f H v c w) (CFun f H' v' c' w').

Definition context_eq (c c' : context) :=
  forall d, context_eq_up_to d c c'.

(** First, some inversion lemmas for pointwise equality of contexts. *)

Lemma ceut_fun_inv :
  forall d f i j H H' (v v' : terms i) c c' (w w': terms j),
    context_eq_up_to (S d) (CFun f H v c w) (CFun f H' v' c' w') ->
    context_eq_up_to d c c'.
Proof.
intros.
dependent destruction H0.
assumption.
Qed.

Lemma ceut_fun_inv_v :
  forall d f i j H H' (v v' : terms i) c c' (w w': terms j),
    context_eq_up_to (S d) (CFun f H v c w) (CFun f H' v' c' w') ->
    forall i, term_eq_up_to d (v i) (v' i).
Proof.
intros.
dependent destruction H0.
apply H1.
Qed.

Lemma ceut_fun_inv_w :
  forall d f i j H H' (v v' : terms i) c c' (w w': terms j),
    context_eq_up_to (S d) (CFun f H v c w) (CFun f H' v' c' w') ->
    forall i, term_eq_up_to d (w i) (w' i).
Proof.
intros.
dependent destruction H0.
apply H3.
Qed.

Lemma context_eq_fun_inv :
  forall f i j H H' (v v' : terms i) c c' (w w': terms j),
    context_eq (CFun f H v c w) (CFun f H' v' c' w') ->
    context_eq c c'.
Proof.
intros f i j H H' v v' c c' w w' H1 d.
apply ceut_fun_inv with (1 := H1 (S d)).
Qed.

Lemma context_eq_fun_inv_v :
  forall f i j H H' (v v' : terms i) c c' (w w': terms j),
    context_eq (CFun f H v c w) (CFun f H' v' c' w') ->
    forall i, term_eq (v i) (v' i).
Proof.
intros f i j H H' v v' c c' w w' H1 k d.
apply ceut_fun_inv_v with (1 := H1 (S d)).
Qed.

Lemma context_eq_fun_inv_w :
  forall f i j H H' (v v' : terms i) c c' (w w': terms j),
    context_eq (CFun f H v c w) (CFun f H' v' c' w') ->
    forall i, term_eq (w i) (w' i).
Proof.
intros f i j H H' v v' c c' w w' H1 k d.
apply ceut_fun_inv_w with (1 := H1 (S d)).
Qed.

Lemma context_eq_fun_inv_symbol :
  forall f i j H (v : terms i) c (w : terms j)
    f' i' j' H' (v' : terms i') c' (w' : terms j'),
    context_eq (CFun f H v c w) (CFun f' H' v' c' w') -> f = f'.
Proof.
intros.
assert (H1 := H0 1).
inversion_clear H1; simpl.
reflexivity.
Qed.

Lemma context_eq_fun_inv_i :
  forall f i j H (v : terms i) c (w : terms j)
    f' i' j' H' (v' : terms i') c' (w' : terms j'),
    context_eq (CFun f H v c w) (CFun f' H' v' c' w') -> i = i'.
Proof.
intros.
assert (H1 := H0 1).
inversion_clear H1; simpl.
reflexivity.
Qed.

Lemma context_eq_fun_inv_j :
  forall f i j H (v : terms i) c (w : terms j)
    f' i' j' H' (v' : terms i') c' (w' : terms j'),
    context_eq (CFun f H v c w) (CFun f' H' v' c' w') -> j = j'.
Proof.
intros.
assert (H1 := H0 1).
inversion_clear H1; simpl.
reflexivity.
Qed.

(** We show pointwise equality and bisimilarity are the same relations. *)

Lemma context_bis_implies_context_eq :
  forall c c', context_bis c c' -> context_eq c c'.
Proof.
intros c c' H d.
revert c c' H.
induction d as [| d IHd]; intros c c' H.
constructor.
destruct H as [| f i j H H' v v' c c' w w' Hv Hc Hw].
constructor.
constructor.
intro k.
apply term_bis_implies_term_eq.
apply Hv.
apply IHd.
exact Hc.
intro k.
apply term_bis_implies_term_eq.
apply Hw.
Qed.

Lemma context_eq_implies_context_bis :
  forall c c', context_eq c c' -> context_bis c c'.
Proof.
induction c as [|f i j H v c IH w]; intros [|f' i' j' H' v' c' w'] H1.
constructor.
assert (H2 := H1 1); inversion H2.
assert (H2 := H1 1); inversion H2.
assert (H2 := context_eq_fun_inv_symbol H1).
assert (H3 := context_eq_fun_inv_i H1).
assert (H4 := context_eq_fun_inv_j H1).
dependent destruction H2.
dependent destruction H3.
dependent destruction H4.
constructor.
intro k.
apply term_eq_implies_term_bis.
apply (context_eq_fun_inv_v H1).
apply IH.
apply (context_eq_fun_inv H1).
intro k.
apply term_eq_implies_term_bis.
apply (context_eq_fun_inv_w H1).
Qed.

Lemma context_bis_context_eq :
  forall c c', context_bis c c' <-> context_eq c c'.
Proof.
split.
apply context_bis_implies_context_eq.
apply context_eq_implies_context_bis.
Qed.

(** We show pointwise equality of contexts is an equivalence. *)

Lemma context_bis_refl :
  forall c, context_bis c c.
Proof.
induction c as [|f i j H v c IH w].
constructor.
constructor.
intro k.
apply term_bis_refl.
exact IH.
intro k.
apply term_bis_refl.
Qed.

Lemma context_bis_symm :
  forall c c', context_bis c c' -> context_bis c' c.
Proof.
induction c as [|f i j H v c IH w]; intros [|f' i' j' H' v' c' w'] H1.
constructor.
inversion H1.
inversion H1.
dependent destruction H1.
constructor.
intro i.
apply term_bis_symm.
apply H1.
apply IH.
assumption.
intro i.
apply term_bis_symm.
apply H3.
Qed.

Lemma context_bis_trans :
  forall c1 c2 c3, context_bis c1 c2 -> context_bis c2 c3 -> context_bis c1 c3.
Proof.
induction c1 as [|f i j H v c IH w]; intros [|f' i' j' H' v' c' w'] [|f'' i'' j'' H'' v'' c'' w''] H1 H2.
constructor.
inversion H2.
constructor.
inversion H1.
inversion H1.
inversion H1.
inversion H2.
dependent destruction H1.
dependent destruction H2.
constructor.
intro.
apply term_bis_trans with (v' i).
apply H1.
apply H5.
apply IH with c'.
assumption.
assumption.
intro.
apply term_bis_trans with (w' i).
apply H4.
apply H7.
Qed.

(* For completeness, we could also show context_eq is an equivalence. *)

(** Filling two bisimilar contexts with the same term yields bisimilar
   contexts. *)
Lemma fill_context_bis :
  forall (c d : context) t,
    context_bis c d ->
    fill c t [~] fill d t.
Proof.
intros c d t H.
revert d H.
induction c as [| f i j H1 v1 c IH v2]; intros d H; destruct d as [| g n m H2 w1 d w2]; simpl.
apply term_bis_refl.
inversion H.
inversion H.
dependent destruction H.
constructor.
intro i.
clear H H'.
apply vcast_intro.
intro k.
clear H1.
clear i H2 g.
induction n as [| n IHn].
simpl in k.
simpl.
dependent destruction k.
simpl.
apply IH.
assumption.
apply H4.
dependent destruction k.
apply H0.
simpl.
specialize IHn with (vtail v1) (vtail w1) k.
apply IHn.
intro i.
unfold vtail.
apply H0.
Qed.

End ContextEquality.


(*Infix " [~] " := context_bis (no associativity, at level 70).*)
(*Infix " [=] " := context_eq (no associativity, at level 70).*)
