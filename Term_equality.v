Require Import Signature.
Require Import Variables.
Require Import Term.

(*
Require Import Equality.
Require Import vector_cast.
*)

Set Implicit Arguments.

Section term_equality.

Variable F : Signature.
Variable X : Variables.

Notation term := (term F X).
Notation terms := (vector term).

(* Bisimilarity on terms *)

CoInductive term_bis : term -> term -> Prop :=
  | Var_bis : forall x, term_bis (Var x) (Var x)
  | Fun_bis : forall (f : F) v w (i : Fin (arity f)), term_bis (v i) (w i) -> term_bis (Fun f v) (Fun f w).

Definition root (t : term) : X + F := 
  match t with 
  | Var x   => inl F x
  | Fun f v => inr X f
  end.


(* equality of infinite terms up to a given depth *)

Inductive term_eq_up_to : nat -> term -> term -> Prop :=
  | teut_0   : forall t u : term, term_eq_up_to 0 t u
  | teut_var : forall n x, term_eq_up_to n (Var x) (Var x)
  | teut_fun : forall n f v w (i : Fin (arity f)), term_eq_up_to n (v i) (w i) -> term_eq_up_to (S n) (Fun f v) (Fun f w).

Definition term_eq (t u : term) := 
  forall n, term_eq_up_to n t u.

Lemma term_bis_implies_term_eq : 
  forall (t u : term), term_bis t u -> term_eq t u.
Proof.
intros t u H n.
generalize t u H; clear H t u.
induction n as [| n IHn]; intros t u H.
constructor.
destruct H.
constructor.
apply teut_fun with (i:=i).
apply IHn with (1:=H).
Qed.

Lemma term_eq_implies_term_bis : forall (t u : term), term_eq t u -> term_bis t u.
Proof.
cofix coIH.
intros [x|f v] [y|g w] H.
assert (H0 := H 7); inversion_clear H0.
constructor.
assert (H0 := H 1); inversion_clear H0.

assert (H0 := H 1); inversion_clear H0.

assert (H0 := H 1); inversion H0.
Require Import Equality.

dependent destruction H5.

simpl.
assert (H0 := term_eq_fun_inv_vec H).
apply Fun_bis.
clear H.
induction v as [|t n v]; dependent destruction w. 
constructor.
destruct (terms_eq_cons_inv H0) as [H1 H2].
constructor.
apply coIH; assumption.

(* hier hebben we hetzelfde probleem als met onze corecursieve id-functie:
   de inductie over vectoren (vector_ind) zit tussen de guard (Fun_bis) 
   en de recursieve aanroep (coIH) in. 
   check maar: 
   Guarded.
*)
Abort.

*)
Infix "[~]" := term_bis (no associativity, at level 70).
Infix "[=]" := term_eq (no associativity, at level 70).

End term_equality.

