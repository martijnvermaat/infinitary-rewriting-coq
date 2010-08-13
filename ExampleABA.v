(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** We construct the TRS with one rule

     ABA : A -> B(A)

   and a convergent reduction of length omega

     A ->> B(B(B(..)))
*)


Require Import Rewriting.

Set Implicit Arguments.


(** * Signature *)


Inductive symbol : Set := A | B.

Definition beq_symb (f g : symbol) : bool :=
  match f, g with
  | A, A => true
  | B, B => true
  | _, _ => false
end.

Lemma beq_symb_ok : forall f g, beq_symb f g = true <-> f = g.
Proof.
(* This should work for any finite inductive symbol type *)
intros f g.
split; intro H.
(* beq_symb f g = true -> f = g *)
  destruct f; destruct g; simpl; (reflexivity || discriminate).
(* f = g ->  beq_symb f g = true *)
  subst g; destruct f; simpl; reflexivity.
Qed.

Definition arity (f : symbol) : nat :=
  match f with
  | A => 0
  | B => 1
  end.


(** * Variables *)


Definition variable : Set := nat.

Fixpoint beq_var (x y : variable) : bool :=
  match x, y with
  | 0, 0       => true
  | S x', S y' => beq_var x' y'
  | _,    _    => false
end.

Lemma beq_var_ok : forall x y, beq_var x y = true <-> x = y.
Proof.
induction x as [|x IH]; destruct y;
  simpl; split; intro H; try (reflexivity || discriminate).
  f_equal. exact (proj1 (IH _) H).
  apply (proj2 (IH _)). inversion H. reflexivity.
Qed.


(** * Terms *)


Definition F : signature := Signature arity beq_symb_ok.
Definition X : variables := Variables beq_var_ok.

Notation term := (term F X).
Notation fterm := (finite_term F X).

(** Function application with no arguments. *)
Notation "f !" := (@Fun F X f (vnil fterm)) (at level 70).
Notation "f !!" := (@FFun F X f (vnil fterm)) (at level 70).

(** Function application with one argument. *)
Notation "f @ a" := (@Fun F X f (vcons a (vnil term))) (right associativity, at level 75).
Notation "f @@ a" := (@FFun F X f (vcons a (vnil fterm))) (right associativity, at level 75).

(** Some terms. *)
Definition test_A : term := A!.
Definition test_BA : term := B @ A!.
Definition test_BBA : term := B @ B @ A!.

(** Finite versions. *)
Definition ftest_A : fterm := A!!.
Definition ftest_BA : fterm := B @@ A!!.
Definition ftest_BBA : fterm := B @@ B @@ A!!.

(** B(B(B(...))). *)
CoFixpoint repeat_B : term :=
  B @ repeat_B.


(** * Contexts *)


Notation context := (context F X).

(** Function application with one argument. *)
Notation "f @@@ a" := (@CFun F X f 0 0 (@refl_equal nat (arity B)) (vnil term) a (vnil term)) (right associativity, at level 75).

Notation id_sub := (empty_substitution F X).


(** * Rewriting *)


Notation trs := (trs F X).

(** Rewrite rule A -> B(A). *)

Definition ABA_l : fterm := A!!.
Definition ABA_r : fterm := B @@ A!!.

Lemma ABA_wf :
  is_var ABA_l = false /\
  incl (vars ABA_r) (vars ABA_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition ABA : rule := Rule ABA_l ABA_r ABA_wf.
Definition ABA_trs : trs := ABA :: nil.

Lemma ABA_left_linear :
  trs_left_linear ABA_trs.
Proof.
constructor; constructor.
Qed.


(** * Rewrite sequences *)


Notation Step := (Step ABA_trs).
Notation Nil := (Nil ABA_trs).

Notation "s [>] t" := (step ABA_trs s t) (at level 40).
Notation "s ->> t" := (sequence ABA_trs s t) (at level 40).

Lemma ABA_in :
  In ABA ABA_trs.
Proof.
left. reflexivity.
Qed.

(** Zero-step rewrite sequence A ->> A. *)
Definition s_A : (A!) ->> (A!) := Nil (A!).

Lemma fact_term_bis_A :
  @Fun F X A (vmap (substitute id_sub) (vnil fterm)) [~] (A !).
Proof.
constructor.
intro.
contradiction (vnil False).
Qed.

Require Import Equality.

Lemma fact_term_bis_BA :
  @Fun F X B (vmap (substitute id_sub) (vcons (A !!) (vnil fterm))) [~] (B @ A !).
Proof.
constructor.
intro i.
dependent destruction i.
apply fact_term_bis_A.
contradiction (vnil False).
Qed.

(** Step A -> B(A). *)
Definition p_A_BA : (A!) [>] (B @ A!) := Step ABA Hole id_sub ABA_in fact_term_bis_A fact_term_bis_BA.

(** Single-step rewrite sequence A ->> B(A). *)
Definition s_A_BA : (A!) ->> (B @ A!) := Cons s_A p_A_BA.

Lemma fact_term_bis_BA' :
  (B @ @Fun F X A (vmap (substitute id_sub) (vnil fterm))) [~]
  (B @ @Fun F X A (fun x : Fin 0 => vnil fterm x)).
Proof.
constructor.
intro i.
dependent destruction i.
apply fact_term_bis_A.
contradiction (vnil False).
Qed.

Lemma fact_term_bis_BBA :
  (B @ @Fun F X B (vmap (substitute id_sub) (vcons (A !!) (vnil fterm)))) [~]
  (B @ B @ @Fun F X A (fun x : Fin 0 => vnil fterm x)).
Proof.
constructor.
intro i.
dependent destruction i.
apply fact_term_bis_BA.
contradiction (vnil False).
Qed.

(** Step B(A) -> B(B(A)). *)
Definition p_BA_BBA : (B @ A!) [>] (B @ B @ A!) := Step ABA (B @@@ Hole) id_sub ABA_in fact_term_bis_BA' fact_term_bis_BBA.

(** Two-step reduction A ->> B(B(A)). *)
Definition s_A_BBA : (A!) ->> (B @ B @ A!) := Cons s_A_BA p_BA_BBA.

(** B(B(...(A)...)) with n applications of B. *)
Fixpoint nB_A (n : nat) : term :=
  match n with
  | 0   => A!
  | S n => B @ (nB_A n)
  end.

(** B(B(...(Hole)...)) with n applications of B. *)
Fixpoint nB_Hole (n : nat) : context :=
  match n with
  | 0   => Hole
  | S n => B @@@ (nB_Hole n)
  end.

Lemma fact_term_bis_nBA :
  forall n,
    fill (nB_Hole n) (@Fun F X A (vmap (substitute id_sub) (vnil fterm))) [~]
    nB_A n.
Proof.
induction n as [| n IH]; simpl; constructor; intro i.
contradiction (vnil False).
dependent destruction i.
apply IH.
contradiction (vnil False).
Qed.

Lemma fact_term_bis_BnBA :
  forall n,
    fill (nB_Hole n) (@Fun F X B (vmap (substitute id_sub) (vcons (A !!) (vnil fterm)))) [~]
    (B @ nB_A n).
Proof.
induction n as [| n IH]; simpl.
apply fact_term_bis_BA.
constructor.
intro i.
dependent destruction i.
apply IH.
contradiction (vnil False).
Qed.

(** Step B(B(...(A)...)) -> B(B(B(...(A)...))) with n applications of B at
   left side. *)
Definition p_nBA_nBBA (n : nat) : (nB_A n) [>] (B @ (nB_A n)) := Step ABA (nB_Hole n) id_sub ABA_in (fact_term_bis_nBA n) (fact_term_bis_BnBA n).

(** n-step rewrite sequence A -1-> B(A) -2-> B(B(A)) -3-> ... -n-> B(B(B(...(A)...)))
   with n applications of B at right side. *)
Fixpoint s_A_nBA (n : nat) : (A!) ->> (nB_A n) :=
  match n as m in nat return (A!) ->> (nB_A m) with
  | 0   => Nil (A!)
  | S n => Cons (s_A_nBA n) (p_nBA_nBBA n)
  end.

Lemma term_eq_up_to_n_nB_A_repeat_B :
  forall n,
    term_eq_up_to n (nB_A n) repeat_B.
Proof.
induction n as [| n IH]; simpl.
constructor.
rewrite (peek_eq repeat_B); simpl.
constructor.
intro i.
dependent destruction i.
apply IH.
dependent destruction i.
Qed.

Lemma converges_nB_A : converges nB_A repeat_B.
Proof.
intro d.
exists d.
intros m H.
simpl.
apply term_eq_up_to_weaken_generalized with m.
assumption.
apply term_eq_up_to_n_nB_A_repeat_B.
Qed.

(** Omega-step reduction A -1-> B(A) -2-> B(B(A)) -3-> ... B(B(B(...))). *)
Definition s_A_repeat_B : (A!) ->> repeat_B :=
  Lim s_A_nBA converges_nB_A.

(** This rewrite sequence is well-formed *)
Lemma wf_s_A_repeat_B :
  wf s_A_repeat_B.
Proof.
split.
induction n; simpl; trivial.
intros n m H.
induction H; simpl.
exists (inl _ tt).
apply embed_refl.
destruct IHle as [i IH].
exists (inr _ i).
assumption.
Qed.


Open Scope ord_scope.


(** Compression lemma is meaningless for this reduction, but
   maybe we should show just that. *)
Lemma length_s_A_repeat_B_le_omega :
  length s_A_repeat_B <= omega.
Proof.
simpl.
constructor.
intro n.
apply ord_le_pd_right with (existT (fun (n : nat) => pd_type n) (S n) (inl _ tt)).
simpl.
induction n as [| n IH]; simpl.
constructor.
apply Ord_le_Succ with (inl (pd_type n) tt).
assumption.
Qed.

(** Let's also show the other direction. *)
Lemma omega_le_length_s_A_repeat_B :
  omega <= length s_A_repeat_B.
Proof.
simpl.
constructor.
intro n.
apply ord_le_pd_right with (existT (fun (n : nat) => pd_type (length (s_A_nBA n))) (S n) (inl _ tt)).
simpl.
induction n as [| n IH]; simpl.
constructor.
apply Ord_le_Succ with (inl (pd_type (length (s_A_nBA n))) tt).
assumption.
Qed.

(** Just because both directions are so similar. *)
Lemma length_s_A_repeat_B_eq_omega :
  length s_A_repeat_B == omega.
Proof.
split; simpl;
  constructor;
  intro n;
  [ apply ord_le_pd_right with (existT (fun (n : nat) => pd_type n) (S n) (inl _ tt))
  | apply ord_le_pd_right with (existT (fun (n : nat) => pd_type (length (s_A_nBA n))) (S n) (inl _ tt)) ];
  induction n as [| n IH]; simpl;
  [ constructor
  | apply Ord_le_Succ with (inl (pd_type n) tt); assumption
  | constructor
  | apply Ord_le_Succ with (inl (pd_type (length (s_A_nBA n))) tt); assumption ].
Qed.


Close Scope ord_scope.
