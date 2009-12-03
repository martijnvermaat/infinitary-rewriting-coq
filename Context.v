Require Export Term.

Set Implicit Arguments.

Section Contexts.

Variable F : Signature.
Variable X : Variables.

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


(*
(* waarom eigenlijk niet de diepte van een context in het type? als volgt: *)

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


End Contexts.
