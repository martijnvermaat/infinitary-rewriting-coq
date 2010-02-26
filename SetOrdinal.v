(* Pre-order on ordinals as defined by Mamane on surreal numbers *)

(*
   This order can be shown to be reflexive and transitive (non-constructively)

   LO_Lte is lte on ordinals
   LO_NGte is the negation of gte on ordinals

   The Ord type inspired on the set type in Benjamin Werner's ZF set theory
   development.
   In the original development by Werner, there are EQ and IN definitions on
   his sets, and I guess lt is just IN. This is copied below.

   I think the trouble with the ordinals-as-sets definitions is that there is
   no clear (to me) way to do ordinal induction.
*)


Inductive Ord : Type :=
  | Ord_cons : forall (i : Type), (i -> Ord) -> Ord.

Definition index (o : Ord) :=
  match o with
  | Ord_cons i f => i
  end.

Definition limit (o : Ord) :=
  match o return (index o) -> Ord with
  | Ord_cons _ f => f
  end.

Inductive lte : Ord -> Ord -> Prop :=
  | Lte_limit : forall o p : Ord,
                (forall a : (index o), ngte (limit o a) p) ->
                lte o p
with ngte : Ord -> Ord -> Prop :=
  | ngte_limit : forall o p : Ord,
                 (exists a : (index p), lte o (limit p a)) -> ngte o p.


(* Below is a verbatim copy of Werner's EQ and IN *)

(* Existential quantification *)
Inductive EXType (P : Type) (Q : P -> Prop) : Prop :=
    EXTypei : forall x : P, Q x -> EXType P Q.

(* Cartesian product in Type *)
Inductive prod_t (A B : Type) : Type :=
    pair_t : A -> B -> prod_t A B.

(* Existential on the Type level *)
Inductive depprod (A : Type) (P : A -> Type) : Type :=
    dep_i : forall x : A, P x -> depprod A P.

(* Recursive Definition of the extentional equality on sets *)
Definition EQ : Ord -> Ord -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType _ (fun x : A => eq1 x (g y))).
Defined.

(* Membership on sets *)
Definition IN (E1 E2 : Ord) : Prop :=
  match E2 with
  | Ord_cons A f => EXType _ (fun y : A => EQ E1 (f y))
  end.
