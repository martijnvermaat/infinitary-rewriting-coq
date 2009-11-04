(*
  A term datatype with fixed symbol arities.
*)


Require Export List.
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

  (* Use names from signature and variables directly *)
  Import S.
  Import X.

  (* Ommit element type and length arguments for vector constructors *)
  Implicit Arguments Vnil [A].
  Implicit Arguments Vcons [A n].

  (* Infinitary term datatype *)
  CoInductive term : Set :=
    | Var : variable -> term
    | Fun : forall f : symbol, vector term (arity f) -> term.

  (* Finitary term datatype *)
  Inductive finite_term : Set :=
    | FVar : variable -> finite_term
    | FFun : forall f : symbol, vector finite_term (arity f) -> finite_term.

  (* Rewriting rule consists of two finite terms *)
  Record rule : Set :=
    makeRule { lhs : finite_term; rhs : finite_term }.

  (* Term rewriting system is a list of rewriting rules *)
  Definition trs : Set := (list rule).

  (* Trivial image of finite_term in term *)
  Fixpoint finite_term_as_term (t : finite_term) : term :=
    match t with
    | FVar x          => Var x
    | FFun f subterms =>
        let fix image_subterms n (terms : vector finite_term n) {struct terms} : (vector term n) :=
          match terms in vector _ n return vector term n with
          | Vnil         => Vnil
          | Vcons u m us => Vcons (finite_term_as_term u) (image_subterms m us)
          end
        in Fun f (image_subterms (arity f) subterms)
    end.

  (* Type of substitutions of terms for variables *)
  Definition substitution := variable -> term.

  (* The identity substitution *)
  Definition empty_substitution (x : variable) : term := Var x.

  (* Apply a substitution to a finite term *)
  Fixpoint substitute (s : substitution) (t : finite_term) {struct t} : term :=
    match t with
    | FVar x          => s x
    | FFun f subterms =>
        let fix subs_subterms n (terms : vector finite_term n) {struct terms} : (vector term n) :=
          match terms in vector _ n return vector term n with
          | Vnil         => Vnil
          | Vcons u m us => Vcons (substitute s u) (subs_subterms m us)
          end
        in Fun f (subs_subterms (arity f) subterms)
    end.

  (* The empty substitution just builds Var terms from variables *)
  Lemma empty_substitution_is_id : forall (x : variable), empty_substitution x = Var x.
  Proof.
    intros.
    unfold empty_substitution.
    reflexivity.
  Qed.

(*
  (* Applying the empty substitution to a finite term gives the trivial infinite term image *)
  Lemma empty_substitution_is_trivial : forall (t : finite_term), (substitute empty_substitution t) = (finite_term_as_term t).
  Proof.
    intros.
    unfold substitute.
    unfold finite_term_as_term.
    induction t.
      (* t = FVar x *)
      apply empty_substitution_is_id.
      (* t = FFun f subterms *)
      (* TODO: Induction principle is probably no good (see ATerm.v in CoLoR) *)
  Abort.
*)

  (* Infinitary one-hole context datatype *)
  CoInductive context : Set :=
    | Hole : context
    | CFun : forall f : symbol, forall i j : nat, i + S j = arity f ->
             vector term i -> context -> vector term j -> context.

  Implicit Arguments CFun [i j].

(*
  Require Import Program.
  Program Fixpoint vector_append n1 n2 (v1 : vector A n1) (v2 : vector A n2) : vector A (n1 + n2) :=
    match v1 with
    | Vnil         => v2
    | Vcons x n xs => Vcons x (vector_append (n1 - 1) n2 xs v2)
    end.
  Next Obligation.
  Next Obligation.
  Defined.
*)

  (* Append two vectors of lengths n1 and n2 yields a vector of length n1 + n2 *)
  Fixpoint vector_append (A : Type) n1 n2 (v1 : vector A n1) (v2 : vector A n2) : vector A (n1 + n2) :=
    match v1 in (vector _ p) return (vector A (p + n2)) with
    | Vnil         => v2
    | Vcons x n xs => Vcons x (vector_append _ n _ xs v2)
    end.

  Implicit Arguments vector_append [A n1 n2].

(*
  (* Fill a context with a term *)
  (*
    Problem:   vector_append gives a vector of length (i + S j) which is equal
               to (arity f), but Coq doesn't know this.
    Solutions: None, casting the vector or typing vector_append differently
               both fail because of guardedness restrictions in CoFixpoint.
  *)
  CoFixpoint fill (c : context) (t : term) : term :=
    match c with
    | Hole                  => t
    | CFun f i j H v1 c' v2 => Fun f (vector_append v1 (Vcons (fill c' t) v2))
    end.
*)

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
        | S m' => Vcons x (vector_cast A n' v' m' _)
        end
    end.

  Implicit Arguments vector_cast [A n m].

(*
  (* Fill a context with a term *)
  (*
    Problem: the call to vector_cast is not guarded, which is required in CoFixpoint, the same
    would apply to a more intelligent version of vector_append.
  *)
  CoFixpoint fill (c : context) (t : term) : term :=
    match c with
    | Hole                  => t
    | CFun f i j H v1 c' v2 => Fun f (vector_cast (vector_append v1 (Vcons (fill c' t) v2)) H)
    end.
*)


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

End Term.
