(*
Add LoadPath "../..".
Require Import Cantor.epsilon0.EPSILON0.

(* If a + 1 < b then a < b *)
Axiom lt_invariant_succ : forall a b, succ a < b -> a < b.

(* If a < b and b < c then a < c *)
Axiom lt_trans : forall a b c, a < b -> b < c -> a < c.

(* Use T1 as type for ordinal numbers *)
Definition Ord := T1.
Delimit Scope cantor_scope with ord.

Close Scope cantor_scope.
*)


Delimit Scope ordinals_scope with ord.

(* Pour man's ordinals *)
Parameter Ord : Type.

Parameter limit : Ord -> Prop.

Parameter succ : Ord -> Ord.

Parameter lt : Ord -> Ord -> Prop.
Notation "o < o'" := (lt o o') : ordinals_scope.

Open Scope ordinals_scope.

(* If a + 1 < b then a < b *)
Axiom lt_invariant_succ : forall a b, succ a < b -> a < b.

(* If a < b and b < c then a < c *)
Axiom lt_trans : forall a b c, a < b -> b < c -> a < c.

Close Scope ordinals_scope.