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
    Choice: how to model rewrite rules with finite lhs (and rhs)?
    1) With type term and a proof that lhs is finite
    2) With new inductive type finite_term
  *)

(*
  Inductive Finite : term \u2192 Prop :=
    | Var_fin : Finite (Var _)
    | Fun_fin : als alle subtermen Finite zijn, dan ook een Fun f (subtermen)
*)



(*

  (*
    Define size on ordinal numbers, so we need a representation
    for ordinal numbers.
  *)
  Fixpoint size (t : term) : nat :=
    match t with
    | Var x          => 0
    | Fun _ subterms =>
        let fix size_subterms n (terms : vector term n) {struct terms} :=
          match terms with
          | Vnil         => 0
          | Vcons u m us => size u + size_subterms m us
        end
        in 1 + (size_subterms _ subterms)
    end.

  (*
    Ordinal numbers:

    1) Casteran: http://www.labri.fr/perso/casteran/Cantor

       Inductive T1 : Set :=
         | zero : T1
         | cons : T1 -> nat -> T1 -> T1.

       cons a n b represents  omega^a *(S n)  + b

    2) Giminez:

       Inductive Ord:Set :=
         | OrdO  : Ord
         | OrdS  : Ord -> Ord
         | Limit : (Nat -> Ord) -> Ord.

       In this representation, a limit ordinal (Limit h) is a sort
       of tree with an infinite width, whose nth child is obtained
       by applying the function h to n.
*)

(*
  Inductive finite_term : Set :=
    | FVar : variable -> finite_term
    | FFun : forall f : symbol, vector finite_term (arity f) -> finite_term.

  Definition rule :=
  Definition trs :=
*)

  (* Substitution *)
  (* Matching *)

End Term.
