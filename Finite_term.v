Require Import List.
Require Import Signature.
Require Import Variables.
Require Export Vector.
Require Import Program.


Set Implicit Arguments.

Section Finite_terms.

Variable F : Signature.
Variable X : Variables.

(* Finitary term datatype *)
Inductive finite_term : Type :=
  | FVar : X -> finite_term
  | FFun : forall f : F, vector finite_term (arity f) -> finite_term.

Notation fterm := (finite_term).
Notation fterms := (vector fterm).

Definition is_var (t : fterm) : bool :=
  match t with 
  | FVar _ => true
  | _      => false
  end.

Definition id := fun t : fterm => t.

Definition mynil : vector fterm 0 := (empty_rect (fun _ => fterm)).

Inductive RR : fterm -> nat -> Prop :=
| RR_var : forall x : X, RR (FVar x) 1
| RR_fun : forall (n : nat) (f : F) (v : fterms (arity f)), RR_vec v n -> RR (FFun f v) (S n)
with RR_vec : forall (m : nat), (fterms m) -> nat -> Prop :=
| RR_vec_nil : RR_vec mynil 0
| RR_vec_cons : forall n1 n2 (t : fterm) m (v : fterms m), RR t n1 -> RR_vec v n2 -> RR_vec (cons t v) (n1 + n2).

Program Fixpoint size (t : fterm) {wf (fun (k : nat) (u : fterm) => RR u k) } : nat :=
  match t with 
  | FVar x => 1
  | FFun f v =>
       let fix size_vec n : (fterms n -> nat) :=
        match n return fterms n -> nat with
	  | 0   => fun _ => 0
          | S n => fun v : fterms (S n) => size (head v) + size_vec n (tail v)
	end
      in size_vec (arity f) v
  end.

Next Obligation of size.
intros H f v H0 H1 _ n w.


compute.
Print S.
Check ( S (w (First n)) <= t ).


(* List of variable occurrences in a finite term *)


Definition vars : fterm -> list X.
intro t; induction t as [x|f v IH].
exact (x :: nil).


Program Fixpoint vars (t : fterm) {struct t} : list X :=
  match t with
  | FVar x   => x :: nil
  | FFun f v =>
      let fix vars_vec n : (fterms n -> list X) :=
        match n return fterms n -> list X with
	  | 0   => fun _ => nil
          | S n => fun v : fterms (S n) => vars (head v) ++ vars_vec n (tail v)
	end
      in vars_vec (arity f) v
  end.



(* A finite term is linear if it has no duplicate variable occurrences *)
Definition linear (t : fterm) : Prop :=
  NoDup (vars t).

End Finite_terms.