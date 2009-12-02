Inductive Ord : Set :=
  | Zero  : Ord
  | Succ  : Ord -> Ord
  | Limit : (nat -> Ord) -> Ord.

(*
  Read:
   surreal numbers in coq
   ordinal theoretic proof theory
   http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html
*)

Parameter lt : Ord -> Ord -> Prop.
Notation "o < o'" := (lt o o') : ordinals_scope.

Delimit Scope ordinals_scope with ord.

Open Scope ordinals_scope.

(* If a + 1 < b then a < b *)
Axiom lt_invariant_succ : forall a b, Succ a < b -> a < b.

(* If a < b and b < c then a < c *)
Axiom lt_trans : forall a b c, a < b -> b < c -> a < c.

Close Scope ordinals_scope.
