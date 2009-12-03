(* Pre-order on limit ordinals as defined by Mamane for surreal numbers *)

(* This order can be shown to be reflexive and transitive (non-constructively)
   but is partial...

   LO_Lte is lte on ordinals
   LO_NGte is the negation of gte on ordinals *)

Inductive LimitOrd : Set :=
  | Limit : (nat -> LimitOrd) -> LimitOrd.

Definition limit (o : LimitOrd) :=
  match o with
  | Limit f => f
  end.

Inductive LO_Lte : LimitOrd -> LimitOrd -> Prop :=
  | Lte_limit : forall o p : LimitOrd,
                (forall n, LO_NGte (limit o n) p) ->
                LO_Lte o p
with LO_NGte : LimitOrd -> LimitOrd -> Prop :=
  | NGte_limit : forall o p : LimitOrd,
                 ex (fun n : nat => LO_Lte o (limit p n)) -> LO_NGte o p.

(*
  Read:
   surreal numbers in coq
   ordinal theoretic proof theory
   http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html
*)

Inductive Ord : Set :=
  | Zero : Ord
  | Succ : Ord -> Ord
  | Lim  : (nat -> Ord) -> Ord.

Parameter lt : Ord -> Ord -> Prop.
Notation "o < o'" := (lt o o') : ordinals_scope.

Delimit Scope ordinals_scope with ord.

Open Scope ordinals_scope.

(* If a + 1 < b then a < b *)
Axiom lt_invariant_succ : forall a b, Succ a < b -> a < b.

(* If a < b and b < c then a < c *)
Axiom lt_trans : forall a b c, a < b -> b < c -> a < c.

Close Scope ordinals_scope.
