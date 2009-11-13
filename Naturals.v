(*
  The natural numbers.
*)

Require Import "../Cantor/epsilon0/EPSILON0".
Require Import Term.
Require Import Rewriting.


(*
  Signature for the natural numbers.
*)
Module NaturalsSignature <: Signature.

  Inductive symbol' : Set := zero | succ | plus.
  Definition symbol := symbol'.

  Lemma eq_symbol_dec : forall f1 f2 : symbol, {f1 = f2} + {f1 <> f2}.
  Proof.
    intros; decide equality.
  Qed.

  Definition arity : symbol -> nat :=
  fun f => match f with
    | zero => 0
    | succ => 1
    | plus => 2
  end.

End NaturalsSignature.




(*
  The natural numbers are defined over the above signature
  and a set of variables.
*)
Module Naturals := Terms NaturalsSignature NatVars.


(* Now play with this *)
Import Naturals.
Import NaturalsSignature.


Module NaturalsSystem <: Trs NaturalsSignature NatVars.

  Module T := Terms NaturalsSignature NatVars.
  Import T.

  Record rule : Set := {
    lhs     : finite_term;
    rhs     : finite_term;
    rule_wf : not_var lhs /\ incl (vars rhs) (vars lhs)
  }.

  Definition trs := list rule.

  Definition rules := nil (A:=rule).

End NaturalsSystem.


Module NatRewriting := Rewriting.Rewriting NaturalsSignature NatVars NaturalsSystem.




Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

(* Some terms *)
Check (Fun plus (Vcons (Fun succ (Vcons (Var 2) Vnil)) (Vcons (Fun zero Vnil) Vnil))).
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
