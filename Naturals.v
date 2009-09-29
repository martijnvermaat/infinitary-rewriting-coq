(*
  The natural numbers.
*)


Require Import Term.


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
Module Naturals := Term.Term NaturalsSignature NatVars.


Import Naturals.
Import NaturalsSignature.

Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

Check (Fun succ (Vcons (Var 1) Vnil)).
Check (Var 3).


CoFixpoint repeat_succ : term :=
  Fun succ (Vcons repeat_succ Vnil).

Check repeat_succ.
