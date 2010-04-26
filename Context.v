Require Import Prelims.
Require Export Term.
Require Export TermEquality.


Set Implicit Arguments.


Section Context.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation terms := (vector term).

(* One-hole contexts where a hole can occur at any finite depth *)
(* TODO: Alternatively define this as term over variables extended with a hole (option variable) *)
Inductive context : Type :=
  | Hole : context
  | CFun : forall (f : F) (i j : nat),
           i + S j = arity f -> terms i -> context -> terms j -> context.

Implicit Arguments CFun [i j].

(* Depth of hole *)
Fixpoint hole_depth c : nat :=
  match c with
  | Hole                => 0
  | CFun _ _ _ _ _ c' _ => 1 + hole_depth c'
  end.

(* Position of hole *)
Fixpoint hole_position c : position :=
  match c with
  | Hole                => nil
  | CFun _ i _ _ _ c' _ => i :: (hole_position c')
  end.

(* Depth of a hole is depth of its position *)
Lemma hole_position_depth :
  forall c,
    hole_depth c = position_depth (hole_position c).
Proof.
induction c; simpl; try (rewrite IHc); reflexivity.
Qed.

(* Fill a hole in a context with a term *)
Fixpoint fill (c : context) (t : term) : term :=
  match c with
  | Hole                  => t
  | CFun f i j H v1 c' v2 => Fun f (vcast (vappend v1 (vcons (fill c' t) v2)) H)
  end.

(* Filling a context gives terms equal up to the hole depth *)
Lemma fill_eq_up_to :
  forall (c : context) t u n,
  n <= hole_depth c -> term_eq_up_to n (fill c t) (fill c u).
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

Lemma hulp : forall n m, n + S (m - S n) = m.
Admitted.

Require Import Lt.
Require Import Bool_nat.

(* Create a context from a term by making a hole *)
Fixpoint dig (t : term) (p : position) {struct p} : option context :=
  match p with
  | nil    => Some Hole
  | n :: p => match t with
              | Var _      => None
              | Fun f args => match lt_ge_dec n (arity f) with
                              | left h  => match dig (vnth h args) p with
                                           | None   => None
                                           | Some c => Some (CFun f (hulp n (arity f))
                                                                  (vtake (lt_le_weak n (arity f) h) args)
                                                                  c
                                                                  (vdrop h args))
                                           end
                              | right _ => None
                              end
              end
  end.

(* Digging a hole and filling it with the same gets you nothing new *)
Lemma dig_fill :
  forall t p,
    match dig t p, subterm t p with
    | Some c, Some s => fill c s [=] t
    | _,      _      => True
    end.
Proof.
intros t p.
induction p as [| n p H]; simpl.
apply term_eq_refl.
admit.
Qed.

(* By the way, CoLoR states the previous lemma like this: *)
Lemma subterm_elim : forall p t s, subterm t p = Some s ->
  {c | dig s p = Some c /\ s [=] fill c s}.
Admitted.


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


Implicit Arguments Hole [F X].
