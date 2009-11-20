Require Export Term.

Section Contexts.

Variable F : Signature.
Variable X : Variables.

Notation term := (term F X).

(* One-hole contexts where a hole can occur at any finite depth *)
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

(* Fill a hole in a context with a term *)
(*
  Again, we are stuck here without some form of casting. Of course,
  the equality we need is in H, so it is easily solved with Program.
  However, Coq crashes, so I can't try it.
*)
(*
  Using latest Coq trunk, there is one obligation generated and it
  is solved automatically.
*)
(*
Program Fixpoint fill (c : context) (t : term) : term :=
  match c with
  | Hole                  => t
  | CFun f i j H v1 c' v2 => Fun f (vappend v1 (vcons (fill c' t) v2))
  end.
*)
Definition fill : context -> term -> term.
Admitted.

End Contexts.
