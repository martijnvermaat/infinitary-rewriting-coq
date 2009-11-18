(*
  The natural numbers.
*)

Require Import Term.
(*Require Import Rewriting.*)


(*
  Signature for the natural numbers.
*)

Inductive symbol : Set := zero | succ | plus.

Lemma eq_symbol_dec : forall f g : symbol, {f = g} + {f <> g}.
Proof.
  decide equality.
Qed.

Definition beq_symb (f g : symbol) : bool :=
  match eq_symbol_dec f g with
  | left  _ => true
  | right _ => false
end.

Lemma beq_symb_ok : forall f1 f2, beq_symb f1 f2 = true <-> f1 = f2.
Proof.
Admitted.

Definition arity (f : symbol) : nat :=
  match f with
  | zero => 0
  | succ => 1
  | plus => 2
  end.

Definition SIG := mkSignature arity beq_symb_ok.

Notation term := (term SIG).
Notation F := (@Fun SIG).
Notation V := (@Var SIG).
Notation vnil := (vnil term).

(* Some terms *)
Check (F zero (vnil)).
Check (V 2).
Check (F plus (vcons (F succ (vcons (V 2) vnil)) (vcons (F zero vnil) vnil))).
Check (F succ (vcons (V 1) vnil)).
Check (V 3).

(* succ(succ(succ(succ(succ(...))))) *)
CoFixpoint repeat_succ : term :=
  F succ (vcons repeat_succ vnil).

Check repeat_succ.

(* Test the head of a term *)
Definition head (t : term) : nat :=
  match t with
  | Var n      => n
  | Fun zero _ => 1005
  | Fun succ _ => 1006
  | Fun plus _ => 1007
  end.

Eval simpl in (head (F plus (vcons (F succ (vcons (V 2) vnil)) (vcons (F zero vnil) vnil)))).
Eval simpl in (head (F succ (vcons (V 1) vnil))).
Eval simpl in (head (V 3)).
Eval simpl in (head repeat_succ).
