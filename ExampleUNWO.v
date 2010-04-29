Require Import Rewriting.

Set Implicit Arguments.

(*
  We construct the weakly orthogonal TRS with rules

    PS : P(S(x)) -> x
    SP : S(P(x)) -> x

  and show it is a counterexample to UN-inf.
*)

(* Signature *)

Inductive symbol : Set := D | U.

Definition beq_symb (f g : symbol) : bool :=
  match f, g with
  | D, D => true
  | U, U => true
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
  | D => 1
  | U => 1
  end.

(* Variables *)

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

(* Terms *)

Definition F : signature := Signature arity beq_symb_ok.
Definition X : variables := Variables beq_var_ok.

Notation term := (term F X).
Notation fterm := (finite_term F X).

(* Variables *)
Notation "x !" := (@FVar F X x) (at level 75).

(* Function application with one argument *)
Notation "f @ a" := (@Fun F X f (vcons a (vnil term))) (right associativity, at level 75).
Notation "f @@ a" := (@FFun F X f (vcons a (vnil fterm))) (right associativity, at level 75).

(* D(D(D(...))) *)
CoFixpoint repeat_D : term :=
  D @ repeat_D.

(* U(U(U(...))) *)
CoFixpoint repeat_U : term :=
  U @ repeat_U.

(* D(U(D(U(...)))) *)
CoFixpoint repeat_DU : term :=
  D @ U @ repeat_DU.

(* Contexts *)

Notation context := (context F X).

(* Function application with one argument *)
Notation "f @@@ a" := (@CFun F X f 0 0 (@refl_equal nat (arity f)) (vnil term) a (vnil term)) (right associativity, at level 75).

Notation id_sub := (empty_substitution F X).

(* Rewriting *)

Notation trs := (trs F X).

(* D(U(x)) -> x *)
Definition DU_l : fterm := D @@ U @@ 1!.
Definition DU_r : fterm := 1!.

Lemma DU_wf :
  is_var DU_l = false /\
  incl (vars DU_r) (vars DU_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition DU : rule := Rule DU_l DU_r DU_wf.

(* U(D(x)) -> x *)
Definition UD_l : fterm := U @@ D @@ 1!.
Definition UD_r : fterm := 1!.

Lemma UD_wf :
  is_var UD_l = false /\
  incl (vars UD_r) (vars UD_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition UD : rule := Rule UD_l UD_r UD_wf.

Definition UNWO_trs : trs := DU :: UD :: nil.

Lemma UNWO_left_linear :
  trs_left_linear UNWO_trs.
Proof.
split; [| split];
  unfold left_linear; unfold linear; simpl;
    constructor.
intro; assumption.
constructor.
intro; assumption.
constructor.
Qed.

(* D(D(D(...))) is infinite *)
Lemma infinite_D :
  infinite repeat_D.
Proof.
intro d.
assert (S : exists p : position, position_depth p = d /\ subterm repeat_D p = Some repeat_D).
exists ((fix z n := match n with O => nil | S n => 0 :: (z n) end) d).
induction d; split.
reflexivity.
reflexivity.
simpl.
f_equal.
apply IHd.
simpl.
apply IHd.
destruct S as [p S].
exists p.
split.
apply S.
rewrite (proj2 S).
discriminate.
Qed.

Require Import Equality.

(* D(D(D(...))) is a normal form *)
Lemma nf_D :
  normal_form (system := UNWO_trs) repeat_D.
Proof.
(* TODO: a lot of this proof is a mess, cleanup
   Also, I expect that this could be generalized and shortened quite a bit
   by using pos_eq. *)
intros [c [r [u [H1 H2]]]].
destruct H1 as [H1 | H1].
rewrite <- H1 in *|-.
clear H1.
assert (H := H2 (S (S (hole_depth c)))).
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
assert (H' := H First).
rewrite (peek_eq repeat_D) in H'.
dependent destruction H'.
assert (H' := H0 First).
simpl in H'.

(* idea, make [=]1 from x0 *)
assert (y0 : term_eq_up_to 1 (@Fun F X D v) (fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm)))))).
(*assert (y0 : @Fun F X D v [=] fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm))))).*)
rewrite x0.
apply term_eq_up_to_refl.
clear x0.

induction c.

assert (H3 := H2 2).
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.
assert (H3 := H1 First).
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.

rewrite (peek_eq repeat_D) in H2.
(*intro x0.*)
assert (d : f = D).
(*assert (y1 := y0 1).*)
inversion_clear y0.
reflexivity.

(*injection x0.
intros _ d.*)
revert e H2 H y0 H0 H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v1 v2.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H y0 H0 H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X D (vcons (fill c (substitute u (lhs DU))) v2)) (D @ repeat_D)).
assert (jaja : fill (@CFun F X D 0 0 e v1 c v2) (substitute u (lhs DU)) = @Fun F X D (vcons (fill c (substitute u (lhs DU))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact (H2 (S n)).
apply (@teut_fun_inv F X n D (vcons (fill c (substitute u (lhs DU))) v2) (vcons repeat_D (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
intro i.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.

clear v0 x H y0 H0 H'.
destruct c.
constructor.
constructor.
simpl.
simpl in H2.
assert (H2' := term_eq_implies_term_bis H2).
dependent destruction H2'.
assert (H3 := H First).
simpl in H3.
clear H2 H.
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.
revert x.
dependent destruction e.
intro y.
simpl in y.
injection y.
intros _ d.
clear y x H v1 v2 v4.
revert e0.
rewrite <- d.
intro e.
constructor.
constructor.

admit. (* same argument as above for r=UD instead of r=DU *)
Admitted.

(* D(D(D(...))) is an infinite normal form *)
Lemma infinite_nf_D :
  infinite repeat_D /\ normal_form (system := UNWO_trs) repeat_D.
Proof.
exact (conj infinite_D nf_D).
Qed.

(* U(U(U(...))) is an infinite normal form *)
Lemma infinite_nf_U :
  infinite repeat_U /\ normal_form (system := UNWO_trs) repeat_U.
Proof.
Admitted.

(* D(D(D(...))) and U(U(U(...))) are different *)
Lemma neq_D_U :
  ~ repeat_D [~] repeat_U.
Proof.
intro H.
rewrite (peek_eq repeat_D), (peek_eq repeat_U) in H.
inversion H.
Qed.

(* D(D(D(...))) and U(U(U(...))) are the only infinite normal forms *)
Lemma only_infinite_nf_D_U :
  forall t,
    infinite t /\ normal_form (system := UNWO_trs) t ->
    t [=] repeat_D \/ t [=] repeat_U.
Proof.
(* We should be able to prove this, but it's probably a lot of work *)
intros [x | [] args] [It Nt].

destruct (It 1) as [p [Dp Hp]].
contradict Hp.
destruct p as [| a [| b p]].
discriminate Dp.
reflexivity.
discriminate Dp.

left.
admit.

right.
admit.
Admitted.

(* Reductions *)
Notation Step := (Step UNWO_trs).
Notation Nil := (Nil UNWO_trs).

Notation "s [>] t" := (step UNWO_trs s t) (at level 40).
Notation "s ->> t" := (sequence UNWO_trs s t) (at level 40).

Generalizable All Variables.

(* D(U(D(U(...)))) rewrites only to itself *)
Lemma rewrites_to_itself_DU :
  forall `(p : repeat_DU [>] t),
    t [=] repeat_DU.
Proof.
intros s p.
dependent destruction p.
destruct i as [H | [H | H]]; try (rewrite <- H in t1, t0; clear H).

induction c as [| f i j e v c IH w]; simpl in t1, t0.
admit. (* from t0 deduce u 1 [=] repeat_DU, then transitivity of [=] *)
apply IH; clear IH.
admit. (* more work *)
admit. (* more work *)

admit. (* same as previous case *)

contradict H.
Qed.

Require Import ZArith.
Delimit Scope Int_scope with I.

Fixpoint sum (n : nat) (t : term) : Z :=
  match n with
  | 0   => Z0
  | S n => match t with
           | Var _      => Z0
           | Fun D args => vfold (-1)%Z Zplus (vmap (sum n) args)
           | Fun U args => vfold (1)%Z  Zplus (vmap (sum n) args)
           end
  end.

(*
Fixpoint fsum (t : fterm) : Z :=
  match t with
  | FVar _      => Z0
  | FFun D args => vfold (-1)%Z Zplus (vmap fsum args)
  | FFun U args => vfold (1)%Z  Zplus (vmap fsum args)
  end.
*)

(* I have no idea how to implement the norm functions *)
