(*
  A term datatype with fixed symbol arities.
*)


Require Export Bvector.


(*
  A Signature contains a decidable set of function symbols and
  an arity function on them.
*)
Module Type Signature.
  Parameter symbol : Set.
  Axiom eq_symbol_dec : forall f1 f2 : symbol, {f1 = f2} + {f1 <> f2}.
  Parameter arity : symbol -> nat.
End Signature.


(*
  A decidable set of variables.
*)
Module Type Variables.
  Parameter variable : Set.
  Axiom eq_variable_dec : forall v1 v2 : variable, {v1 = v2} + {v1 <> v2}.
End Variables.


(*
  A concrete implementation of a set of variables using the
  natural numbers.
*)
Module NatVars <: Variables.

  Definition variable := nat.

  Lemma eq_variable_dec : forall v1 v2 : variable, {v1 = v2} + {v1 <> v2}.
  Proof.
    intros; decide equality.
  Qed.

End NatVars.


(*
  A Term module uses a Signature and a set of variables and
  provides a term datatype over them.
*)
Module Term (S : Signature) (X : Variables).

  Import S.
  Import X.

  Notation symbol := S.symbol.
  Notation variable := X.variable.

  CoInductive term : Set :=
    | Var : variable -> term
    | Fun : forall f : symbol, vector term (arity f) -> term.

(*
  Definition size (t : term) : nat :=
    match t with
    | Var x          => 0
    | Fun _ subterms =>
        let fix size_subterms (terms : vector term _) {struct terms} :=
          match terms with
          | Vnil         => 0
          | Vcons u _ us => size u + size_subterms us
        end
        in 1 + (size_subterms subterms)
    end.
*)

  (* Definition finite : (t : term) : bool := exists n (size t = n). *)

  (* Definieer rewrite rule met predicate finite voor beide kanten van de rule *)

  (* Substitution *)
  (* Matching *)

End Term.
