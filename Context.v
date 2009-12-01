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

End Contexts.
