(*
  Read:
   surreal numbers in coq
   ordinal theoretic proof theory
   http://www4.informatik.tu-muenchen.de/~isabelle/html-data/library/HOL/Induct/Tree.html

  We can also choose to represent a limit by a stream instead of a function...
*)

Inductive Ord : Set :=
  | Zero  : Ord
  | Succ  : Ord -> Ord
  | Limit : (nat -> Ord) -> Ord.

(* Below are the definitions by muad (Coq-Club, 2009-11-25) for the Peter
   Hancock notes. He mentions that already proving reflexivity of <= seems
   hard.

   NB: I don't claim to understand the Peter Hancock notes at this time. *)

Definition Fam (A : Type) : Type := { I : Set & I -> A }.
Definition Pow (A : Type) : Type := A -> Set.

Fixpoint Pd (o : Ord) : Set :=
  match o with
  | Zero    => False
  | Succ o' => (unit + Pd o') % type
  | Limit l => { n : nat & Pd (l n) }
  end.

Definition zero z := Pd z -> False.

Notation "!" := (False_rect _).

Fixpoint Pd_pd (o : Ord) : Pd o -> Ord :=
  match o with
  | Zero    => !
  | Succ o' => fun i => match i with
                        | inl tt => o'
                        | inr t  => Pd_pd o' t
                        end
  | Limit l => fun i => match i with
                        | existT n t => Pd_pd (l n) t
                        end
  end.

Definition pd (o : Ord) : Fam Ord := existT _ (Pd o) (Pd_pd o).

Fixpoint Ord_le (o p : Ord) : Set :=
  match o with
  | Zero    => unit
  | Succ o' => { t : Pd p & Ord_le o' (Pd_pd p t) }
  | Limit l => forall n : nat, Ord_le (l n) p
  end.

Definition Ord_eq (o p : Ord) := (Ord_le o p, Ord_le p o).

Definition Ord_lt (o p : Ord) := { t : Pd p & Ord_le o (Pd_pd p t) }.

(* proof reflexivity *)
