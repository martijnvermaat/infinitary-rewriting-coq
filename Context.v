Require Import Prelims.
Require Export Term.
Require Export TermEquality.


Set Implicit Arguments.


Section Context.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).

(* One-hole contexts where a hole can occur at any finite depth *)
(* TODO: Alternatively define this as term over variables extended with a hole (option variable) *)
Inductive context : Type :=
  | Hole : context
  | CFun : forall (f : F) (i j : nat),
           i + S j = arity f -> vector term i -> context -> vector term j -> context.

Implicit Arguments CFun [i j].

(* Depth of hole *)
Fixpoint hole_depth c :=
  match c with
  | Hole                => 0
  | CFun _ _ _ _ _ c' _ => 1 + hole_depth c'
  end.

(* Fill a hole in a context with a term *)
Fixpoint fill (c : context) (t : term) : term :=
  match c with
  | Hole                  => t
  | CFun f i j H v1 c' v2 => Fun f (vcast (vappend v1 (vcons (fill c' t) v2)) H)
  end.

(* Filling a context gives terms equal up to the hole depth *)
Lemma fill_eq_up_to :
  forall (c : context) t u n,
  hole_depth c > n -> term_eq_up_to n (fill c t) (fill c u).
Proof.
intros c t u n.
revert c.
induction n; simpl.
constructor.
destruct c; simpl; intro H.
inversion H.
constructor.
revert v e.
generalize (arity f).
induction i; simpl; intro a.
intros _ e k.
destruct k; repeat (rewrite vcast_vcons).
apply IHn.
auto with arith.
apply term_eq_refl.
intros v e k.
destruct k; repeat (rewrite vcast_vcons).
apply term_eq_refl.
apply IHi.
Qed.


(*
(* TODO: waarom eigenlijk niet de diepte van een context in het type? als volgt: *)

Inductive context : nat -> Type :=
  | Hole : context 0
  | CFun : forall (d : nat) (f : F) (n m : nat), n + S m = arity f ->
           vector term n -> context d -> vector term m -> context (S d).

(* dan natuurlijk:
Definition hole_depth (d : nat) (c : context d) := d.
*)

(* Fill a hole in a context with a term *)
Fixpoint fill (d : nat) (c : context d) (t : term) : term :=
  match c with
  | Hole                  => t
  | CFun _ f i j H v1 c' v2 => Fun f (vcast (vappend v1 (vcons (fill c' t) v2)) H)
  end.

(*

- een gevolg zal dan zijn, dat ook steps geparameteriseerd worden met de diepte
(is dat handig?)

- een andere vraag die opkomt is: waarom parameteriseren we niet meteen met de positie van de hole ...

*)
*)


End Context.
