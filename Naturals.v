(*
  The natural numbers.
*)

Require Import Rewriting.

(* Signature *)

Inductive symbol : Set := zero | succ | plus.

Definition beq_symb (f g : symbol) : bool :=
  match f, g with
  | zero, zero => true
  | succ, succ => true
  | plus, plus => true
  | _,    _    => false
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
  | zero => 0
  | succ => 1
  | plus => 2
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

Definition Sigma := mkSignature arity beq_symb_ok.
Definition X := mkVariables beq_var_ok.

(* Infinite terms *)
Notation term := (term Sigma X).
Notation F := (@Fun Sigma X).
Notation V := (@Var Sigma X).

(* Finite terms *)
Notation fterm := (finite_term Sigma X).
Notation FF := (@FFun Sigma X).
Notation FV := (@FVar Sigma X).

Notation fvnil := (vnil fterm).
Notation vnil := (vnil term).

(* Some terms *)
(*
Check (F zero (vnil)).
Check (V 2).
Check (F plus (vcons (F succ (vcons (V 2) vnil)) (vcons (F zero vnil) vnil))).
Check (F succ (vcons (V 1) vnil)).
Check (V 3).
*)

(* succ(succ(succ(succ(succ(...))))) *)
CoFixpoint repeat_succ : term :=
  F succ (vcons repeat_succ vnil).

(*
Check repeat_succ.
*)

(* Test the head of a term *)
Definition head (t : term) : nat :=
  match t with
  | Var n      => n
  | Fun zero _ => 1005
  | Fun succ _ => 1006
  | Fun plus _ => 1007
  end.

(*
Eval simpl in (head (F plus (vcons (F succ (vcons (V 2) vnil)) (vcons (F zero vnil) vnil)))).
Eval simpl in (head (F succ (vcons (V 1) vnil))).
Eval simpl in (head (V 3)).
Eval simpl in (head repeat_succ).
*)

(* Rewriting *)

(* We build the rewrite rule succ(x)->x *)

Definition succ_x_x_l : fterm := FF succ (vcons (FV 1) fvnil).
Definition succ_x_x_r : fterm := FV 1.

Lemma succ_x_x_wf : is_var succ_x_x_l = false /\
                    incl (vars succ_x_x_r) (vars succ_x_x_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

(*
Definition succ_x_x : rule := mkRule Sigma X succ_x_x_l succ_x_x_r succ_x_x_wf.
Definition succ_x_x_trs : (trs Sigma X) := succ_x_x :: nil.
*)
