Require Import RewritingOrdinalSequence.

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
Notation "f @ a" := (@Fun F X f (Vcons a Vnil)) (right associativity, at level 75).
Notation "f @@ a" := (@FFun F X f (Vcons a Vnil)) (right associativity, at level 75).

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
Notation "f @@@ a" := (@CFun F X f 0 0 (@refl_equal nat (arity f)) Vnil a Vnil) (right associativity, at level 75).

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

Require Import Equality.

(* D(D(D(...))) is an infinite normal form *)
Lemma infinite_nf_D :
  ~ finite repeat_D /\ normal_form (system := UNWO_trs) repeat_D.
Proof.
split.
intros [t H].
(*
induction t as [x | t args IH].
unfold repeat_D in H.
admit. (* discriminate H. *)
admit.
intros [c [r [u [H1 H2]]]].
destruct H1 as [H1 | H1].
assert (H := H2 (hole_depth c)). (* probably depth + 1 needed *)
dependent destruction H.
admit. (* c = Hole, so D(U(x)) [=] repeat_D *)
admit. (* lhs r is not a variable *)
admit. (* repeat_D cannot be equal to D _and_ U *)
admit. (* same argument as previous case *)
*)
admit.
admit.
Qed.

(* U(U(U(...))) is an infinite normal form *)
Lemma infinite_nf_U :
  ~ finite repeat_U /\ normal_form (system := UNWO_trs) repeat_U.
Proof.
Admitted.

(* D(D(D(...))) and U(U(U(...))) are the only infinite normal forms *)
Lemma only_infinite_nf_D_U :
  forall t,
    ~ finite t /\ normal_form (system := UNWO_trs) t ->
    t [=] repeat_D \/ t [=] repeat_U.
Proof.
(* No idea if we can prove this *)
Admitted.

(* Reductions *)
Notation Step := (Step UNWO_trs).
Notation Nil := (Nil UNWO_trs).

Notation "s [>] t" := (step UNWO_trs s t) (at level 40).
Notation "s ->> t" := (sequence UNWO_trs s t) (at level 40).

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

(*
Fixpoint sum (n : nat) (t : term) : Z :=
  match n with
  | 0   => Z0
  | S n => match t with
           | Var _      => Z0
           | Fun D args => Vfold (-1)%Z Zplus (vmap (sum n) args)
           | Fun U args => Vfold (1)%Z  Zplus (vmap (sum n) args)
           end
  end.
*)

(*
Fixpoint fsum (t : fterm) : Z :=
  match t with
  | FVar _      => Z0
  | FFun D args => vfold (-1)%Z Zplus (vmap fsum args)
  | FFun U args => vfold (1)%Z  Zplus (vmap fsum args)
  end.
*)

(* I have no idea how to implement the norm functions *)
