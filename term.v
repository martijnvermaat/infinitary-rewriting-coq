Require Import Bvector.


Module Type Signature.
  Parameter symbol : Set.
  Axiom eq_symbol_dec : forall f1 f2 : symbol, {f1 = f2} + {f1 <> f2}.
  Parameter arity : symbol -> nat.
End Signature.


Module Type Variables.
  Parameter variable : Set.
  Axiom eq_variable_dec : forall v1 v2 : variable, {v1 = v2} + {v1 <> v2}.
End Variables.


Module Term (S : Signature) (X : Variables).

  Import S.
  Import X.

  Notation symbol := S.symbol.
  Notation variable := X.variable.

  CoInductive term : Set :=
    | Var : variable -> term
    | Fun : forall f:symbol, vector term (arity f) -> term.

End Term.


Module PeanoSignature <: Signature.

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

End PeanoSignature.


Module Vars <: Variables.
  Definition variable := nat.
  Lemma eq_variable_dec : forall v1 v2 : variable, {v1 = v2} + {v1 <> v2}.
  Proof.
    intros; decide equality.
  Qed.
End Vars.


Module Peano := Term (PeanoSignature) Vars.


Import Peano.
Import PeanoSignature.
Import Vars.

Print vector.
Check (Fun PeanoSignature.succ (Vcons term (Var 1) 0 (Vnil term))).
Check (Var 3).

(*
CoFixpoint repeat_succ (n : nat) : term :=
  Fun PeanoSignature.succ (Vcons term (repeat_succ n) 0 (Vnil term)))
*)
