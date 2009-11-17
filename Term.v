Require Export List.
Require Export Bvector.
Require Import Signature.
Require Import Variables.
Require Import Finite_term.

Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

Set Implicit Arguments.

Section Terms.

Variable F : Signature.
Variable X : Variables.

(* infinite terms *)
CoInductive term : Type :=
  | Var : X -> term
  | Fun : forall f : F, vector term (arity f) -> term.

Notation terms := (vector term).
Notation fterm := (finite_term F X).
Notation fterms := (vector fterm).

(* Trivial image of finite_term in term *)
Fixpoint finite_term_as_term (t : fterm) : term :=
  match t with
  | FVar x   => Var x
  | FFun f v =>
      let fix fterms_as_terms n (v : fterms n) {struct v} : terms n :=
        match v in vector _ n return vector term n with
	| Vnil         => Vnil
	| Vcons u m us => Vcons (finite_term_as_term u) (fterms_as_terms m us)
	end
      in Fun f (fterms_as_terms (arity f) v)
  end.

(* Type of substitutions of terms for variables *)
Definition substitution := X -> term.

(* The identity substitution *)
Definition empty_substitution (x : X) : term := Var x.

(* Apply a substitution to a finite term *)

Fixpoint substitute (s : substitution) (t : fterm) {struct t} : term :=
  match t with
  | FVar x   => s x
  | FFun f v =>
	  let fix substitute_vec n (v : fterms n) {struct v} : terms n :=
		match v in vector _ n return terms n with
		| Vnil         => Vnil
		| Vcons u m us => Vcons (substitute s u) (substitute_vec m us)
		end
	  in Fun f (substitute_vec (arity f) v)
  end.

Print substitute.

(* The empty substitution just builds Var terms from variables *)
Lemma empty_substitution_is_id : forall (x : X), empty_substitution x = Var x.
Proof.
  reflexivity.
Qed.

(* Applying the empty substitution to a finite term gives the trivial infinite term image *)
Lemma empty_substitution_is_trivial : 
  forall (t : finite_term), (substitute empty_substitution t) = (finite_term_as_term t).
Proof.
  induction t as [x|f v]; simpl.
	(* t = FVar x *)
	apply empty_substitution_is_id.
	(* t = FFun f subterms *)
	(* TODO: Induction principle is probably no good (see ATerm.v in CoLoR) *)
Abort.
*)

(* One-hole contexts where a hole can occur at any finite dept *)
(* TODO: Alternatively define this as term over variables extended with a hole (option variable) *)
Inductive context : Type :=
  | Hole : context
  | CFun : forall f : F, forall i j : nat, i + S j = arity f ->
			 vector term i -> context -> vector term j -> context.

Implicit Arguments CFun [i j].

(* Depth of hole *)
Fixpoint hole_depth c :=
  match c with
  | Hole                => 0
  | CFun _ _ _ _ _ c' _ => 1 + hole_depth c'
  end.

(* Appending two vectors of lengths n1 and n2 yields a vector of length n1 + n2 *)
Fixpoint vector_append (A : Type) n1 n2 (v1 : vector A n1) (v2 : vector A n2) : vector A (n1 + n2) :=
  match v1 in (vector _ p) return (vector A (p + n2)) with
  | Vnil         => v2
  | Vcons x n xs => Vcons x (vector_append xs v2)
  end.

Implicit Arguments vector_append [A n1 n2].

(* Cast a vector of length n to a vector of length m, having that n = m *)
Require Import Program.
Program Fixpoint vector_cast (A : Type) n (v : vector A n) m (H : n = m) {struct v} : vector A m :=
  match v with
  | Vnil =>
	  match m with
	  | 0 => Vnil
	  | _ => !
	  end
  | Vcons x n' v' =>
	  match n with
	  | 0 => !
	  | S m' => Vcons x (vector_cast v' _ (m:=m'))
	  end
  end.

Implicit Arguments vector_cast [A n m].

(* Fill a hole in a context with a term *)
Fixpoint fill (c : context) (t : term) : term :=
  match c with
  | Hole                  => t
  | CFun f i j H v1 c' v2 => Fun f (vector_cast (vector_append v1 (Vcons (fill c' t) v2)) H)
  end.

(* Vectors v and w are pair-wise in relation R *)
Fixpoint vector_for_all2 (A B : Type) (R : A -> B -> Prop) n m (v : vector A n) (w : vector B m) {struct v} : Prop :=
  match v, w with
  | Vnil,         Vnil         => True
  | Vcons a _ v', Vcons b _ w' => R a b /\ vector_for_all2 R v' w'
  | _,            _            => False
  end.

End Terms.

Implicit Arguments Var [X F].
Implicit Arguments FVar [X F].

(* once more, but now out of the section: *)
Implicit Arguments mkSignature [symbol beq_symb].
Implicit Arguments arity [s].
Implicit Arguments beq_symb [s].
Implicit Arguments beq_symb_ok [s x y].
