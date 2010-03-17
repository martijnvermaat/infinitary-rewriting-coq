Require Import RewritingOrdinalSequence.

(*
  TRS with rule A -> B(A)
*)


(* Signature *)

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

Definition F := Signature arity beq_symb_ok.
Definition X := Variables beq_var_ok.

Notation term := (term F X).
Notation fterm := (finite_term F X).

(* Function application with no arguments *)
Notation "f !" := (@Fun F X f (vnil term)) (at level 70).
Notation "f !!" := (@FFun F X f (vnil fterm)) (at level 70).

(* Function application with one argument *)
Notation "f @ a" := (@Fun F X f (vcons a (vnil term))) (right associativity, at level 75).
Notation "f @@ a" := (@FFun F X f (vcons a (vnil fterm))) (right associativity, at level 75).

(* Some terms *)
Check (A!).
Check (A!!).
Check (B @ A!).
Check (B @@ A!!).
Check (B @ B @ A!).
Check (B @@ B @@ A!!).

(* B B B B B B ... *)
CoFixpoint repeat_B : term :=
  B @ repeat_B.

(* Rewriting *)

(* A -> B(A) *)

Definition ABA_l := A!!.
Definition ABA_r := B @@ A!!.

Lemma ABA_wf :
  is_var ABA_l = false /\
  incl (vars ABA_r) (vars ABA_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition ABA := Rule ABA_l ABA_r ABA_wf.
Definition ABA_trs := ABA :: nil.

Lemma ABA_left_linear :
  trs_left_linear ABA_trs.
Proof.
split; constructor.
Qed.

(* Reductions *)
Notation Step := (Step ABA_trs).
Notation Nil := (Nil ABA_trs).

Variable s : step ABA_trs (A!) (A!).
Check (Nil (A!)).
Check (Cons (Nil (A!)) s).

(* Two step reduction A -> B(A) -> B(B(A)) *)
