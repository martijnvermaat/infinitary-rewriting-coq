Section dList.

(* Inductive-recursive definition of lists with distinct natural numbers *)

(* See capreta's induction-recursion paper *)

(* Original inductive-recursive definition, not for Coq *)

(*
Inductive dList : Set :=
  | dnil  : dList
  | dcons : forall (n : nat) (l : dList) (h : (Fresh l n)), dList.

Fixpoint Fresh (l : dList) (n : nat) : Prop :=
  match l with
  | dnil          => True
  | dcons n' l' h => n <> n' /\ (Fresh l' n).
*)

Inductive dList' : Type :=
  | dnil'  : dList'
  | dcons' : forall (Y : Type) (j : Y -> dList') (f : Y -> nat -> Prop) (n : nat) (l : Y) (h : (f l n)), dList'.

Inductive Fresh' : dList' -> nat -> Prop :=
  | fnil  : forall (n : nat), Fresh' dnil' n
  | fcons : forall (Y : Type) (j : Y -> dList') (Fr : Y -> nat -> Prop) (n' : nat) (l : Y) (h : Fr l n') (n : nat),
            n <> n' -> (Fr l n) -> Fresh' (dcons' Y j Fr n' l h) n.

(* Error: Universe Inconsistency *)
(*
Inductive Freshc : dList' -> Prop :=
  | nilc  : Freshc dnil'
  | consc : forall (n' : nat) (l : dList') (h : Freshc l) (p : Fresh' l n'),
            Freshc (dcons' dList' (fun z => z) Fresh' n' l p).
*)

(* Now define define the original type with sum over dList' *)

End dList.
