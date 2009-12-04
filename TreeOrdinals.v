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

Definition Fam (A : Type) : Type := { I : Type & I -> A }.
Definition Pow (A : Type) : Type := A -> Set.

Fixpoint Pd (o : Ord) : Type :=
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

(*
Fixpoint Ord_le (o p : Ord) : Type :=
  match o with
  | Zero    => unit
  | Succ o' => { t : Pd p & Ord_le o' (Pd_pd p t) }
  | Limit l => forall n : nat, Ord_le (l n) p
  end.
*)

Inductive Ord_le : Ord -> Ord -> Type :=
  | Ord_le_Zero : forall o, Ord_le Zero o
  | Ord_le_Succ : forall (alpha beta : Ord) (p : Pd beta),
                  Ord_le alpha (Pd_pd beta p) -> Ord_le (Succ alpha) beta
  | Ord_le_Limit : forall (f : nat -> Ord) (beta : Ord), 
                   (forall n, Ord_le (f n) beta) -> Ord_le (Limit f) beta. 


(*
Lemma kantine :
  forall (alpha beta : Ord) (t : Pd beta),
  Ord_le (Succ alpha) beta -> Ord_le alpha (Pd_pd beta t).
Proof.
intros.
inversion_clear X.
(* ? *)

*)

Lemma le_LimO_r : forall alpha f n,
  Ord_le alpha (f n) ->
  Ord_le alpha (Limit f).
Proof.
induction alpha.
intros.
constructor.
intros f n H.
inversion_clear H.
apply Ord_le_Succ with (p:=existT (fun n => Pd (f n)) n p).
simpl.
assumption.
intros.
constructor.
intro m.
apply (X m f n).
inversion_clear X0.
apply X1.
Qed. 

Lemma Ord_le_refl : forall o : Ord, Ord_le o o.
Proof.
induction o.
simpl.
exact tt.

constructor.
inversion IHo.
simpl.



Definition Ord_eq (o p : Ord) := (Ord_le o p, Ord_le p o).

Definition Ord_lt (o p : Ord) := { t : Pd p & Ord_le o (Pd_pd p t) }.

