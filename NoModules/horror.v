Require Import Term.

Set Implicit Arguments.

Lemma disc_O_S : forall n, O <> S n.
Proof.
intros n H.
discriminate H.
Qed.

Lemma disc_S_O : forall n, S n <> O.
Proof.
intros n H.
discriminate H.
Qed.

Definition S_eq (n m : nat) (H : n = m) : S n = S m := f_equal S H.
Definition S_eq_inv (n m : nat) (H : S n = S m) : n = m := eq_add_S n m H.

(*
Implicit Arguments disc_S_O [n].
Implicit Arguments disc_O_S [n].
Implicit Arguments S_eq [n m].
Implicit Arguments S_eq_inv [n m].
Implicit Arguments Vnil [A].
Implicit Arguments Vcons [n A].
*)

(***********************************************************************************************)
(*

(*
 hiermee kreeg ik allerlei vreemde bewijstermen te zien 
 (in de trant van vector_cast_proof_obligation4 etc.) 
 toen ik met een versie van terms_bis_ind bezig was.
 het loont misschien de moeite dat nog eens te proberen.
 iets anders is de import van Program die ook axioms 
 over JMeq met zich meebrengt ...
*)

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

*)
(***********************************************************************************************)

(***********************************************************************************************)
(*

(* this works *)

Definition vector_cast (A : Type) (n : nat) (v : vector A n) (m : nat) (H : n = m) : vector A m :=
  match H in (_ = m) return (vector A m) with
    refl_equal => v
end.

(* but the disadvantage is that vector_cast does not `go over' Vcons, i.e. no conversion, 
  and I also do not see how to prove it: *)

Lemma vector_cast_Vcons (A : Type) : 
  forall (n : nat) (v : vector A n) (m : nat) (H : n = m) (a : A), 
  vector_cast (Vcons a v) (S_eq H) = Vcons a (vector_cast v H).

Lemma vector_cast_Vcons2 (A : Type) : 
  forall (n : nat) (v : vector A n) (m : nat) (H1 : S n = S m) (H2 : n = m) (a : A), 
  vector_cast (Vcons a v) H1 = Vcons a (vector_cast v H2).

(* moreover how to prove: *)

Lemma vector_cast_proof_irrelevance :
  forall (A : Type) (n : nat) (v : vector A n) (m : nat) (H1 H2 : n = m),
  vector_cast v H1 = vector_cast v H2.
*)  
(***********************************************************************************************)

Fixpoint vector_cast (A : Type) (n : nat) (v : vector A n) (m : nat) {struct v} : n = m -> vector A m :=
  match v in (vector _ p) return (p = m -> (vector A m)) with
    Vnil =>
      match m return 0 = m -> vector A m with
        0 => fun _ => Vnil
      | m' => fun H => False_rect (vector A m') (disc_O_S H)
      end
  | Vcons a n' v' => 
	  match m return S n' = m -> vector A m with
	    0    => fun H => False_rect (vector A 0) (disc_S_O H)
	  | S m' => fun H => Vcons a (vector_cast v' (S_eq_inv H))
	  end
  end.

Lemma vector_cast_proof_irrelevance :
  forall (A : Type) (n : nat) (v : vector A n) (m : nat) (H1 H2 : n = m),
  vector_cast v H1 = vector_cast v H2.
Proof.
induction v as [|a n v IH]; destruct m as [|m]; simpl; intros H1 H2.
reflexivity.
discriminate H1.
discriminate H1.
apply f_equal.
apply IH.
Qed.

(*
(* this one occurs in Color's VecUtil.v, but that imports JMeq ... (just like Program does) *)
Lemma Vcons_inv (A : Type) : 
  forall (a b : A) (n : nat) (v : vector A n) (m : nat) (Hnm : n = m) (w : vector A m), 
  Vcons a v = Vcons b w -> a = b /\ v = w.
Proof.
induction v as [|c n v IH]; intros.
destruct w as [|d m w].
*)


Section Bisimilarity.

Variable Sig : Signature.
Variable X : Variables.

Notation term := (term Sig X).
Notation terms := (vector term).

Notation Var := (Var Sig X).
Notation Fun := (Fun Sig X).
Notation arity := (arity Sig).
(* better to make Sig and X globally implicit for the term constructors *)

(* Bisimilarity on terms *)

CoInductive term_bis : term -> term -> Prop :=
  | Var_bis : forall x : X, term_bis (Var x) (Var x)
  | Fun_bis : forall (f : Sig) (v w : terms (arity f)),
              terms_bis v w -> term_bis (Fun f v) (Fun f w)

with terms_bis : forall (n : nat), (terms n) -> (terms n) -> Prop :=
  | Vnil_bis  : terms_bis 0 Vnil Vnil
  | Vcons_bis : forall (t u : term) (n : nat) (v w : terms n),
                term_bis t u -> terms_bis n v w -> terms_bis (S n) (Vcons t v) (Vcons u w).

(* cf.
CoInductive bis : stream -> stream -> Prop :=
  bis_intro :
    forall xs ys,
    head xs = head ys -> 
    bis (tail xs) (tail ys) -> 
    bis xs ys.
*)


(*
Fixpoint terms_bis_ind 
  (P : forall n : nat, terms n -> terms n -> Prop) :
  (Hnil :P 0 Vnil Vnil)
  (Hcons : forall (t u : term) (n : nat) (v w : terms n),
    term_bis t u -> terms_bis n v w -> P n v w -> P (S n) (Vcons t v) (Vcons u w)
  ) ->
  forall (n : nat) (v : terms n) {struct v} : 
  forall (w : terms n), terms_bis n v w -> P n v w :=
  match v in terms n return forall (w : terms n), terms_bis -> P n v w.
*)

Lemma terms_bis_ind :
  forall (P : forall n : nat, terms n -> terms n -> Prop),
  P 0 Vnil Vnil ->
  ( forall (t u : term) (n : nat) (v w : terms n),
    term_bis t u -> terms_bis n v w -> P n v w -> P (S n) (Vcons t v) (Vcons u w)
  ) ->
  forall (n : nat) (v w : terms n), terms_bis n v w -> P n v w.
Proof.
Admitted.
(*
intros P H H0.
induction v as [|t n v IH]; intros w H1.
(* a familiar traumatic situation:
   we have that [w : terms 0] but how to get it equal to Vnil ... *)
(* this does not work: *)
generalize H; clear H.
set (n := 0); cut (n = 0); [ | reflexivity].
destruct H1.
intros Hn H.
exact H.

*)


(* this won't work; in need of JMeq again? *)
(*
Lemma terms_bis_Vcons_inv : 
  forall ........
*)

(*
Lemma terms_bis_ind : (* or, welcome to the coq horror show *)
  forall (P : forall n : nat, terms n -> terms n -> Prop),
  (forall (m : nat) (Hm0 : m = 0) (w : terms m), P 0 Vnil (vector_cast w Hm0)) ->
  ( forall (t u : term) (n : nat) (v : terms n) (m : nat) (w : terms m) (Hmn : m = n) (HSmSn : S m = S n) (* (S_eq Hmn) *),
    term_bis t u -> terms_bis n v (vector_cast w Hmn) -> P n v (vector_cast w Hmn) -> P (S n) (Vcons t v) (vector_cast (Vcons u w) HSmSn)
  ) ->
  forall (n : nat) (v : terms n) (m : nat) (Hmn : m = n) (w : terms m),
  terms_bis n v (vector_cast w Hmn) -> P n v (vector_cast w Hmn).
Proof.
intros P Hnil Hcons.
induction v as [|t n v IHv]; destruct w as [|u m w]; intros H.
apply Hnil.
discriminate Hmn.
discriminate Hmn.
simpl.
simpl in H.
*)

Inductive term_eq_up_to : nat -> term -> term -> Prop :=
    eut_0   : forall t u : term, term_eq_up_to 0 t u
  | eut_var : forall (n : nat) (x : variable), term_eq_up_to n (Var x) (Var x)
  | eut_fun : forall (n : nat) (f : symbol) (v w : terms (arity f)), 
              terms_eq_up_to n (arity f) v w -> term_eq_up_to (S n) (Fun f v) (Fun f w)

with terms_eq_up_to : nat -> forall m : nat, vector term m -> vector term m -> Prop :=
    eutv_nil  : forall (n : nat), terms_eq_up_to n 0 Vnil Vnil
  | eutv_cons : forall (n : nat) (t u : term), term_eq_up_to n t u -> 
                forall (m : nat) (v w : terms m), terms_eq_up_to n m v w -> 
                terms_eq_up_to n (S m) (Vcons t v) (Vcons u w).

Definition term_eq (t u : term) := forall (n : nat), term_eq_up_to n t u.
Definition terms_eq (m : nat) (v w : terms m) := forall (n : nat), terms_eq_up_to n m v w.

Lemma terms_eq_up_to_0 : forall (m : nat) (v w : terms m), terms_eq_up_to 0 m v w.
Proof.
induction v as [|t n v IH].



(* now, with terms_eq_ind this works: *)
Lemma term_bis_to_term_eq : forall (t u : term), term_bis t u -> term_eq t u.
Proof.
intros t u H n.
generalize t u H; clear H t u.
induction n as [| n IHn]; intros t u H.
constructor.
destruct H.
constructor.
constructor.
induction H as [|t u m v w H H0 IHterms]; constructor.
apply IHn with (1:=H).
exact IHterms.
Qed.


Lemma term_eq_var_inv : forall (x y : variable), term_eq (Var x) (Var y) -> x = y.
Proof.
intros x y H.
assert (H0 := H 1).
inversion_clear H0.
reflexivity.
Qed.

(*
Lemma term_eq_fun_inv : 
  forall (f g : symbol) (v : terms (arity f)) (w : terms (arity g)),
  term_eq (Fun f v) (Fun g w) -> f = g /\ terms_eq ... 
(that f = g does not yet give that their arities are equal 
 and hence we cannot write the second conjunct ...)

*)

Lemma term_eq_fun_inv_symbol : 
  forall (f g : symbol) (v : terms (arity f)) (w : terms (arity g)),
  term_eq (Fun f v) (Fun g w) -> f = g.
Proof.
intros f g v w H.
assert (H0 := H 1).
inversion_clear H0; simpl.
reflexivity.
Qed.

Print f_equal.

Lemma term_eq_fun_inv_vector :
  forall (n : nat) (f g : symbol) (v : terms (arity f)) (w : terms (arity g)),
  term_eq_up_to (S n) (Fun f v) (Fun g w) ->
  forall (Hgf : g = f),
  terms_eq_up_to n (arity f) v (vector_cast w (f_equal arity Hgf)).
Proof.
induction n as [|n IHn]; simpl.
intros f g v w H Hgf.
inversion H.
simpl.
ass
inversion_clear H.


Lemma term_eq_to_term_bis : forall (t u : term), term_eq t u -> term_bis t u.
Proof.
cofix coIH.
intros [x|f v] [y|g w] H.
rewrite term_eq_var_inv with (1:=H).
constructor.
assert (H0 := H 1); inversion_clear H0.
assert (H0 := H 1); inversion_clear H0.

(* now this 
rewrite term_eq_fun_inv_symbol with (1:=H).

ofcourse yields:

Error: Abstracting over the term "f" leads to a term
"fun f : symbol => term_bis (Fun f v) (Fun g w)" which is ill-typed.
*)

(*
apply Fun_bis.
*)


End Term.


