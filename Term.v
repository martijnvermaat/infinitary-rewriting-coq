(*
  A term datatype with fixed symbol arities.
*)


Require Export List.
Require Export Bvector.

Add LoadPath "../".
Require Import Cantor.epsilon0.EPSILON0.
Close Scope cantor_scope.


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

  (* Omit element type and length arguments for vector constructors *)
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

  (* List of variable occurrences in finite term *)
  (* TODO: alternatively use Coq.FSets *)
  Fixpoint vars (t : finite_term) : list variable :=
    match t with
    | FVar x          => x :: nil
    | FFun f subterms =>
        let fix vars_subterms n (terms : vector finite_term n) {struct terms} : list variable :=
          match terms with
          | Vnil         => nil
          | Vcons u m us => vars u ++ vars_subterms m us
          end
        in vars_subterms (arity f) subterms
    end.

  (* Rewriting rule consists of two finite terms *)
  (* TODO: explore alternative using 'term' with proof of finiteness *)
  Record rule : Set := {
    lhs : finite_term;
    rhs : finite_term;
    wf  : incl (vars rhs) (vars lhs)
  }.

  (* Term rewriting system is a list of rewriting rules *)
  Definition trs : Set := (list rule).

(*
  (* This is ill-formed, because the recursive call to id is not guarded *)
  CoFixpoint id (t : term) : term :=
    match t with
    | Var x => Var x
    | Fun f subterms => 
        let fix id_subterms n (terms : vector term n) {struct terms} : (vector term n) :=
          match terms in vector _ n return vector term n with
          | Vnil         => Vnil
          | Vcons u m us => Vcons (id u) (id_subterms m us)
          end
        in Fun f (id_subterms (arity f) subterms)
    end.
*)

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

  (* One-hole contexts where a hole can occur at any finite dept *)
  Inductive context : Set :=
    | Hole : context
    | CFun : forall f : symbol, forall i j : nat, i + S j = arity f ->
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
    | Vcons x n xs => Vcons x (vector_append _ n _ xs v2)
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
        | S m' => Vcons x (vector_cast A n' v' m' _)
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
    | Vcons a _ v', Vcons b _ w' => R a b /\ vector_for_all2 A B R _ _ v' w'
    | _,            _            => False
    end.

  Implicit Arguments vector_for_all2 [A B n m].

(*
  (* Bisimilarity on terms *)

  (*
    Error: Non strictly positive occurrence of "term_eq"
    http://pauillac.inria.fr/pipermail/coq-club/2005/001897.html
  *)
  CoInductive term_eq : term -> term -> Prop :=
    | VarEq : forall x : variable, term_eq (Var x) (Var x)
    | FunEq : forall f : symbol, forall subterms1 subterms2 : vector term (arity f),
                 vector_for_all2 term_eq subterms1 subterms2 -> term_eq (Fun f subterms1) (Fun f subterms2).

  (* Error: Recursive definition on "term" which should be an inductive type *)
  Fixpoint term_eq (t u : term) {struct t} : Prop :=
    match t, u with
    | Var x,    Var y    => if eq_variable_dec x y then True else False
    | Fun f t', Fun g v' => (if eq_symbol_dec f g then True else False) /\ vector_for_all2 term_eq t' v'
    | _,        _        => False
    end.

  (* Error: Parameters should be syntactically the same for each inductive type *)
  CoInductive term_eq : term -> term -> Prop :=
    | VarEq : forall x : variable, term_eq (Var x) (Var x)
    | FunEq : forall f : symbol, forall subterms1 subterms2 : vector term (arity f),
                 terms_eq subterms1 subterms2 -> term_eq (Fun f subterms1) (Fun f subterms2)
  with terms_eq n m : (vector term n) -> (vector term m) -> Prop :=
    | Vnil_eq  : terms_eq Vnil Vnil
    | Vcons_eq : forall t u : term, forall v : (vector term _), forall w : (vector term _),
                   term_eq t u -> terms_eq v w -> terms_eq (Vcons t _ v) (Vcons u _ w).
*)

  (* Bisimilarity on terms *)
  CoInductive term_eq : term -> term -> Prop :=
    | VarEq : forall x : variable, term_eq (Var x) (Var x)
    | FunEq : forall f : symbol, forall subterms1 subterms2 : vector term (arity f),
                 terms_eq (arity f) subterms1 subterms2 -> term_eq (Fun f subterms1) (Fun f subterms2)
  with terms_eq : forall n : nat, (vector term n) -> (vector term n) -> Prop :=
    | Vnil_eq  : terms_eq 0 Vnil Vnil
    | Vcons_eq : forall t u : term, forall n : nat, forall v w : (vector term n),
                   term_eq t u -> terms_eq n v w -> terms_eq (S n) (Vcons t v) (Vcons u w).

  (* Reduction step *)
  Inductive step : Set :=
    | Step : context -> rule -> substitution -> step.

  Definition source (u : step) : term :=
    match u with
    | Step c r s => fill c (substitute s (lhs r))
    end.

  Definition target (u : step) : term :=
    match u with
    | Step c r s => fill c (substitute s (rhs r))
    end.

  Definition depth (u : step) : nat :=
    match u with
    | Step c r s => hole_depth c
    end.

  Open Scope cantor_scope.

  (* If a + 1 < b then a < b *)
  Axiom lt_invariant_succ : forall a b, succ a < b -> a < b.

  (* If a < b and b < c then a < c *)
  Axiom lt_trans : forall a b c, a < b -> b < c -> a < c.

  (* Reduction sequence *)
  Record sequence : Set := {
      length   : T1;
      steps    : forall a : T1, a < length -> step;
      matching : forall a : T1, forall H : succ a < length,
                   term_eq (target (steps a (lt_invariant_succ a length H)))
                           (source (steps (succ a) H));
      (* forall a : limit ordinal < length, forall n, exists b < a,
           forall c, b < c < a -> depth of hole in step c > n *)
      limits : forall a k n, forall H1 : omega_term a k < length,
                 exists b, b < omega_term a k ->
                 forall c, b < c -> forall H2 : c < omega_term a k,
                 depth (steps c (lt_trans c (omega_term a k) length H2 H1)) > n
  }.

  Close Scope cantor_scope.


  (*
    Ordinal numbers:

    1) Casteran: http://www.labri.fr/perso/casteran/Cantor

       Countable ordinals up to phi0 in Cantor Normal Form:

       Inductive T1 : Set :=
         | zero : T1
         | cons : T1 -> nat -> T1 -> T1.

       cons a n b represents  omega^a *(S n)  + b

       Type T2 contains countable ordinals up to gamma0 in Veblen Normal Form.

    2) Gimenez:

       Inductive Ord:Set :=
         | OrdO  : Ord
         | OrdS  : Ord -> Ord
         | Limit : (Nat -> Ord) -> Ord.

       In this representation, a limit ordinal (Limit h) is a sort
       of tree with an infinite width, whose nth child is obtained
       by applying the function h to n.

  *)

End Term.
