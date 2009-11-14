(*
  A term datatype with fixed symbol arities.
*)

Require Export List.
Require Export Bvector.

(* Omit element type and length arguments for vector constructors *)
Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

Set Implicit Arguments.

Section Term.

(*
  A Signature contains a decidable set of function symbols and
  an arity function on them.
*)
Record Signature : Type := mkSignature {
  symbol :> Set;
  arity : symbol -> nat;
  beq_symb : symbol -> symbol -> bool;
  beq_symb_ok : forall x y, beq_symb x y = true <-> x = y
}.

Implicit Arguments mkSignature [symbol beq_symb].
Implicit Arguments arity [s].
Implicit Arguments beq_symb [s].
Implicit Arguments beq_symb_ok [s x y].

(*
  A decidable set of variables.
*)
Record Variables : Type := mkVariables {
  variable :> Type;
  beq_var : variable -> variable -> bool;
  beq_var_ok : forall x y, beq_var x y = true <-> x = y
}.

(*
  A Term module uses a Signature and a set of variables and
  provides a term datatype over them.
*)

Variable Sig : Signature.
Variable X : Variables.

(* Infinitary term datatype *)
CoInductive term : Type :=
  | Var : X -> term
  | Fun : forall f : Sig, vector term (arity f) -> term.

(* Finitary term datatype *)
Inductive finite_term : Type :=
  | FVar : X -> finite_term
  | FFun : forall f : Sig, vector finite_term (arity f) -> finite_term.

(* Finite term is not a variable *)
Definition not_var t :=
  match t with
  | FVar _   => False
  | FFun _ _ => True
  end.

  (* List of variable occurrences in finite term *)
  (* TODO: alternatively use Coq.FSets *)
  Fixpoint vars (t : finite_term) : list X :=
    match t with
    | FVar x          => x :: nil
    | FFun f subterms =>
        let fix vars_subterms n (terms : vector finite_term n) {struct terms} : list X :=
          match terms with
          | Vnil         => nil
          | Vcons u m us => vars u ++ vars_subterms m us
          end
        in vars_subterms (arity f) subterms
    end.

  (* A finite term is linear if it has no duplicate variable occurrences *)
  Definition linear (t : finite_term) : Prop :=
    NoDup (vars t).

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
  Definition substitution := X -> term.

  (* The identity substitution *)
  Definition empty_substitution (x : X) : term := Var x.

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
  Lemma empty_substitution_is_id : forall (x : X), empty_substitution x = Var x.
  Proof.
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
  (* TODO: Alternatively define this as term over variables extended with a hole (option variable) *)
  Inductive context : Type :=
    | Hole : context
    | CFun : forall f : Sig, forall i j : nat, i + S j = arity f ->
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


  (* Bisimilarity on terms *)
  CoInductive term_eq : term -> term -> Prop :=
    | VarEq : forall x : X, term_eq (Var x) (Var x)
    | FunEq : forall f : Sig, forall subterms1 subterms2 : vector term (arity f),
                 terms_eq subterms1 subterms2 -> term_eq (Fun f subterms1) (Fun f subterms2)
  with terms_eq : forall n : nat, (vector term n) -> (vector term n) -> Prop :=
    | Vnil_eq  : terms_eq Vnil Vnil
    | Vcons_eq : forall t u : term, forall n : nat, forall v w : (vector term n),
                   term_eq t u -> terms_eq v w -> terms_eq (Vcons t v) (Vcons u w).

  Inductive equal_up_to : nat -> term -> term -> Prop :=
      eut_0   : forall t u : term, equal_up_to 0 t u
    | eut_var : forall n : nat, forall x : X, equal_up_to n (Var x) (Var x)
    | eut_fun : forall n : nat, forall f : Sig, forall v w : vector term (arity f), 
                equal_up_to_vec n v w -> equal_up_to (S n) (Fun f v) (Fun f w)
  with equal_up_to_vec : nat -> forall m : nat, vector term m -> vector term m -> Prop :=
      eutv_nil  : forall n, equal_up_to_vec n Vnil Vnil
    | eutv_cons : forall n,  
                  forall t u : term, equal_up_to n t u -> 
                  forall m : nat, forall v w : vector term m, equal_up_to_vec n v w -> 
                  equal_up_to_vec n (Vcons t v) (Vcons u w).

End Term.

Implicit Arguments Var [X Sig].

(* once more, out of the section *)
Implicit Arguments mkSignature [symbol beq_symb].
Implicit Arguments arity [s].
Implicit Arguments beq_symb [s].
Implicit Arguments beq_symb_ok [s x y].
