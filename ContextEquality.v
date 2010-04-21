Require Import Signature.
Require Import Variables.
Require Import Context.
Require Import Equality.


Set Implicit Arguments.


Section ContextEquality.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation terms := (vector term).
Notation context := (context F X).

(*
   TODO: we might need proof irrelevance here for the
       H : i = S j + arity f
   arguments of CFun.
*)

(* Bisimilarity on contexts *)
Inductive context_bis : context -> context -> Prop :=
  | Hole_bis : context_bis Hole Hole
  | CFun_bis : forall f i j H (v v' : terms i) c c' (w w' : terms j),
               (forall i, term_bis (v i) (v' i)) ->
               context_bis c c' ->
               (forall i, term_bis (w i) (w' i)) ->
               context_bis (CFun f H v c w) (CFun f H v' c' w').

(* Equality of contexts up to a given depth *)
Inductive context_eq_up_to : nat -> context -> context -> Prop :=
  | ceut_0    : forall c c' : context, context_eq_up_to 0 c c'
  | ceut_hole : forall n, context_eq_up_to n Hole Hole
  | ceut_cfun : forall n f i j H (v v' : terms i) c c' (w w' : terms j),
                (forall i, term_eq_up_to n (v i) (v' i)) ->
                context_eq_up_to n c c' ->
                (forall i, term_eq_up_to n (w i) (w' i)) ->
                context_eq_up_to (S n) (CFun f H v c w) (CFun f H v' c' w').

Definition context_eq (c c' : context) :=
  forall n, context_eq_up_to n c c'.

End ContextEquality.


(*Infix " [~] " := context_bis (no associativity, at level 70).*)
(*Infix " [=] " := context_eq (no associativity, at level 70).*)
