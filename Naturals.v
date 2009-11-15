(*
  The natural numbers.
*)

Require Import Term.
Require Import Rewriting.


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

Definition sig := mkSignature arity beq_symb_ok.

Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

(* Some terms *)
Check (@Fun sig plus (Vcons (Fun succ (Vcons (Var 2) Vnil)) (Vcons (Fun zero Vnil) Vnil))).
Check (Fun succ (Vcons (Var 1) Vnil)).
Check (Var 3).

(* succ(succ(succ(succ(succ(...))))) *)
CoFixpoint repeat_succ : term :=
  Fun succ (Vcons repeat_succ Vnil).

Check repeat_succ.

(* Test the head of a term *)
Definition head (t : term) : nat :=
  match t with
  | Var n      => n
  | Fun zero _ => 1005
  | Fun succ _ => 1006
  | Fun plus _ => 1007
  end.

Eval simpl in (head (Fun plus (Vcons (Fun succ (Vcons (Var 2) Vnil)) (Vcons (Fun zero Vnil) Vnil)))).
Eval simpl in (head (Fun succ (Vcons (Var 1) Vnil))).
Eval simpl in (head (Var 3)).
Eval simpl in (head repeat_succ).
