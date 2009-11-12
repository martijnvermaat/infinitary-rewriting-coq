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
(*  Require Import Program.
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
*)

Definition vector_cast (A : Type) (n : nat) (v : vector A n) (m : nat) (H : n = m) : vector A m :=
  match H in (_ = m) return (vector A m) with
    refl_equal => v
  end.

Implicit Arguments vector_cast [A n m].

Lemma disc_O_S : forall n, O <> S n.Proof.
intros n H.discriminate H.Qed.
Lemma disc_S_O : forall n, S n <> O.Proof.
intros n H.discriminate H.Qed.
Definition S_eq (n m : nat) (H : n = m) : S n = S m :=
  f_equal S H.

Definition S_eq_inv (n m : nat) (H : S n = S m) : n = m := eq_add_S n m H.

Implicit Arguments disc_S_O [n].
Implicit Arguments disc_O_S [n].
Implicit Arguments S_eq [n m].
Implicit Arguments S_eq_inv [n m].

Fixpoint vector_cast2 (A : Type) (n : nat) (v : vector A n) (m : nat) {struct v} : n = m -> vector A m :=
  match v in (vector _ p) return (p = m -> (vector A m)) with
    Vnil => 
      match m return 0 = m -> vector A m with
        0 => fun _ => Vnil 
      | m' => fun H => False_rect (vector A m') (disc_O_S H) 
      end
  | Vcons a n' v' => 
      match m return S n' = m -> vector A m with
        0    => fun H => False_rect (vector A 0) (disc_S_O H) 
      | S m' => fun H => Vcons a (vector_cast2 A n' v' m' (S_eq_inv H))
      end
  end.

Implicit Arguments vector_cast2 [A n m].


(*
Lemma Vcons_inv (A : Type) : 
  forall (a b : A) (n : nat) (v : vector A n) (m : nat) (Hnm : n = m) (w : vector A m), 
  Vcons a v = Vcons b w -> a = b /\ v = w.
Proof.
induction v as [|c n v IH]; intros.
destruct w as [|d m w].
*)
Lemma vector_cast2_proof_irrelevance :
  forall (A : Type) (n : nat) (v : vector A n) (m : nat) (H1 H2 : n = m),
  vector_cast2 v H1 = vector_cast2 v H2.
Proof.
induction v as [|a n v IH]; destruct m as [|m]; simpl; intros H1 H2.
reflexivity.
discriminate H1.
discriminate H1.
apply f_equal.
apply IH.
Qed.


(*
Lemma vector_cast_proof_irrelevance :
  forall (A : Type) (n : nat) (v : vector A n) (m : nat) (H1 H2 : n = m),
  vector_cast v H1 = vector_cast v H2.
(*compute.*)
dependent inversion_clear H1.
clear m.
intro H2.
(* no no no *)

(*
dependent inversion H2 with 
(fun (p : nat) (w : vector A p) => forall (H : p = n), vector_cast v (refl_equal n) = vector_cast w H).
  (forall (x : (eq n)), 
   vector_cast v (refl_equal n) = vector_cast v H2
intros.
compute.
destruct H1.
*)
Admitted.
*)

Lemma vector_cast_Vcons (A : Type) : forall (n : nat) (v : vector A n) (m : nat) (H : n = m) (a : A), 
  vector_cast (Vcons a v) (S_eq H) = Vcons a (vector_cast v H).
Proof.
Admitted.
(* ! *)

Lemma vector_cast_Vcons2 (A : Type) : forall (n : nat) (v : vector A n) (m : nat) (H1 : S n = S m) (H2 : n = m) (a : A), 
  vector_cast (Vcons a v) H1 = Vcons a (vector_cast v H2).
Proof.
Admitted.
(* ! *)

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

  (* Bisimilarity on terms *)

  CoInductive term_bis : term -> term -> Prop :=
    | Var_bis : forall x : variable, term_bis (Var x) (Var x)
    | Fun_bis : forall f : symbol, forall v w : vector term (arity f),
                terms_bis (arity f) v w -> term_bis (Fun f v) (Fun f w)

  with terms_bis : forall n : nat, (vector term n) -> (vector term n) -> Prop :=
    | Vnil_bis  : terms_bis 0 Vnil Vnil
    | Vcons_bis : forall t u : term, forall n : nat, forall v w : (vector term n),
                  term_bis t u -> terms_bis n v w -> terms_bis (S n) (Vcons t v) (Vcons u w).

Print vector.

Inductive myvector : nat -> Type :=
    myVnil  : myvector 0
  | myVcons : term -> forall n : nat, myvector n -> myvector (S n).

Notation terms := (vector term).

(*
Program Fixpoint terms_bis_ind (P : forall n : nat, terms n -> terms n -> Prop) :
  (Hnil : P 0 Vnil Vnil) ->
  (Hcons : forall (t u : term) (n : nat) (v w : terms n),
    term_bis t u -> terms_bis n v w -> P n v w -> P (S n) (Vcons t v) (Vcons u w)
  )
  (n : nat) (v : terms n) {struct v} : forall (w : terms n), terms_bis n v w -> P n v w :=
  match v with
    Vnil => 
      match w with 
        Vnil => P0
      | _    => !
      end
   | Vcons n v => 
       match w with 
         Vnil => !
       | Vcons m w =
.... pfff
*)

(*
Lemma terms_bis_ind :
  forall (P : forall n : nat, terms n -> terms n -> Prop),
  P 0 Vnil Vnil ->
  ( forall (t u : term) (n : nat) (v w : terms n),
    term_bis t u -> terms_bis n v w -> P n v w -> P (S n) (Vcons t v) (Vcons u w)
  ) ->
  forall (n : nat) (v w : terms n), terms_bis n v w -> P n v w.
Proof.
intros P H H0.
induction v; intros w H1.
generalize H; clear H.
set (n := 0); cut (n = 0); [ | reflexivity].
destruct H1.
intros Hn H.
exact H.
(* what !? *)
*)

Variable point : nat.


(* this won't work; in need of JMeq again? *)

Lemma terms_bis_Vcons_inv : 
  forall ........


Lemma terms_bis_ind : (* or, welcome to the coq horror show *)
  forall (P : forall n : nat, terms n -> terms n -> Prop),
  (forall (m : nat) (Hm0 : m = 0) (w : terms m), P 0 Vnil (vector_cast2 w Hm0)) ->
  ( forall (t u : term) (n : nat) (v : terms n) (m : nat) (w : terms m) (Hmn : m = n) (HSmSn : S m = S n) (* (S_eq Hmn) *),
    term_bis t u -> terms_bis n v (vector_cast2 w Hmn) -> P n v (vector_cast2 w Hmn) -> P (S n) (Vcons t v) (vector_cast2 (Vcons u w) HSmSn)
  ) ->
  forall (n : nat) (v : terms n) (m : nat) (Hmn : m = n) (w : terms m),
  terms_bis n v (vector_cast2 w Hmn) -> P n v (vector_cast2 w Hmn).
Proof.
intros P Hnil Hcons.
induction v as [|t n v IHv]; destruct w as [|u m w]; intros H.
apply Hnil.
discriminate Hmn.
discriminate Hmn.
simpl.
simpl in H.

inversion H.

rewrite 

Check terms_bis_Vcons_inv.

rewrite vector_cast_Vcons2 with (H2 := (S_eq_inv Hmn)) in H.



inversion H.

destruct H.


apply Hcons with (Hmn := S_eq_inv Hmn).



reflexivity.


generalize HSmSn H; clear H HSmSn.
dependent inversion HSmSn.

(* damn! why does vector_cast not go over Vcons ? *)



(*
Lemma terms_eq_ind : forall m, P : vector term m
*)

Inductive term_eq_up_to : nat -> term -> term -> Prop :=
    eut_0   : forall t u : term, term_eq_up_to 0 t u
  | eut_var : forall n : nat, forall x : variable, term_eq_up_to n (Var x) (Var x)
  | eut_fun : forall n : nat, forall f : symbol, forall v w : vector term (arity f), 
              term_eq_up_to_vec n (arity f) v w -> term_eq_up_to (S n) (Fun f v) (Fun f w)
with term_eq_up_to_vec : nat -> forall m : nat, vector term m -> vector term m -> Prop :=
    eutv_nil  : forall n, terms_eq_up_to n 0 Vnil Vnil
  | eutv_cons : forall n,  
                forall t u : term, term_eq_up_to n t u -> 
                forall m : nat, forall v w : vector term m, terms_eq_up_to n m v w -> 
                terms_eq_up_to n (S m) (Vcons t v) (Vcons u w).

(*

Lemma term_bis_root : 

*)

Lemma term_bis_to_term_eq_up_to_n :
  forall n, 
  forall t u : term,
  term_bis t u ->
  term_eq_up_to n t u.
Proof.



induction n as [| n IH]; intros t u H.
constructor.
destruct H.
constructor.
constructor.


destruct H; constructor.
apply IH.
exact H.



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


Variable term_eq_up_to : nat -> term -> term -> Prop.

Definition Ord := T1.
Variable limit : Ord -> Prop.

  (* Strongly continuous rewriting sequences *)
  Record sequence : Set := {
      length   : T1;
      steps    : forall a : T1, a < length -> step;
      continuous_local : 
               forall a : T1, forall H : succ a < length,
               term_bis (target (steps a (lt_invariant_succ a length H))) (source (steps (succ a) H));

      continuous_limit : 
               forall a : Ord, limit a ->  
               forall H1 : a < length,
               forall n : nat, 
               exists b, b < a /\
               forall c, b < c -> forall H2 : c < a,
               term_eq_up_to n (source (steps c (lt_trans c a length H2 H1))) (source (steps a H1));

      continuous_strong : 
               forall a : Ord, limit a -> 
               forall H1 : a < length,
               forall n : nat, 
               exists b, 
               b < a /\
               forall c, b < c -> forall H2 : c < a,
               depth (steps c (lt_trans c a length H2 H1)) > n
  }.

  Definition weakly_convergent : sequence -> Prop := 
    approaching length, forall n, eventually prefix_n is stable

  Definition strongly_convergent : sequence -> Prop := 
    exists t : term,
    approaching length, forall n, eventually depth of redex > n
    /\ 

  Lemma strong_implies_weak

  Close Scope cantor_scope.

Print epsilon.

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
