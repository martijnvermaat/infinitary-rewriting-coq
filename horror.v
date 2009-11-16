Require Import Term.
Require Import Equality.
(*
Require Import vector_cast.
*)

Set Implicit Arguments.

Section term_equality.

Variable F : Signature.
Variable X : Variables.

Notation term := (term F X).
Notation terms := (vector term).

(* Bisimilarity on terms *)

CoInductive term_bis : term -> term -> Prop :=
  | Var_bis : forall x, term_bis (Var x) (Var x)
  | Fun_bis : forall f v w, terms_bis v w -> term_bis (Fun f v) (Fun f w)

with terms_bis : forall n, terms n -> terms n -> Prop :=
  | Vnil_bis  : terms_bis Vnil Vnil
  | Vcons_bis : forall t u n (v w : terms n), 
                term_bis t u -> terms_bis v w -> terms_bis (Vcons t v) (Vcons u w).

Definition root (t : term) : X + F := 
  match t with 
  | Var x   => inl x
  | Fun f v => inr f
  end.

Lemma terms_bis_Vcons_inv : 
  forall t u n (v w : terms n),
  terms_bis (Vcons t v) (Vcons u w) -> term_bis t u /\ terms_bis v w.
Proof.
intros t u n v w H.
dependent destruction H.
split; assumption.
Qed.

(*
Lemma terms_bis_ind_cast :
  forall (P : forall n, terms n -> terms n -> Prop),
  P 0 Vnil Vnil ->
  ( forall t u n (v : terms n) m (w : terms m) (Hmn : m = n) 
    (w' := vector_cast w Hmn),
    term_bis t u -> terms_bis v w' -> P n v w' -> P (S n) (Vcons t v) (Vcons u w')
  ) ->
  forall n (v : terms n) m (Hmn : m = n) (w : terms m) (w' := vector_cast w Hmn),
  terms_bis v w' -> P n v w'.
Proof.
intros P Hnil Hcons.
induction v as [|t n v IHv]; destruct w as [|u m w]; simpl; intro H.
apply Hnil.
discriminate Hmn.
discriminate Hmn.
destruct terms_bis_Vcons_inv with (1:=H) as [H1 H2].
apply Hcons with (1:=H1) (2:=H2).
apply IHv with (1:=H2).
Qed.
*)

Lemma terms_bis_ind :
  forall (P : forall n : nat, terms n -> terms n -> Prop),
  P 0 Vnil Vnil ->
  ( forall (t u : term) (n : nat) (v w : terms n),
    term_bis t u -> terms_bis v w -> P n v w -> P (S n) (Vcons t v) (Vcons u w)
  ) ->
  forall (n : nat) (v w : terms n), terms_bis v w -> P n v w.
Proof.
(*
intros P Hnil Hcons n v w H.
assert (Hcast := vector_cast_simpl w (refl_equal n)).
rewrite <- Hcast.
apply terms_bis_ind_cast; simpl.
exact Hnil.
intros t u p xs q ys Hqp H1 H2 H3.
apply Hcons with (1:=H1) (2:=H2) (3:=H3).
rewrite Hcast.
exact H.
(* more directly (no use of [terms_bis_ind_cast], using the tactics from Equality.v 
  (incorporating axiom [JMeq_eq]) : 
*)
Restart.
*)
intros P Hnil Hcons.
induction v as [|t n v IHv]; dependent destruction w; simpl; intro H.
apply Hnil.
dependent destruction H.
apply Hcons. 
assumption.
assumption.
apply IHv.
assumption.
Qed.

(* equality of infinite terms up to a given depth *)

Inductive term_eq_up_to : nat -> term -> term -> Prop :=
  | teut_0   : forall t u : term, term_eq_up_to 0 t u
  | teut_var : forall n x, term_eq_up_to n (Var x) (Var x)
  | teut_fun : forall n f v w, 
               terms_eq_up_to n v w -> term_eq_up_to (S n) (Fun f v) (Fun f w)

with terms_eq_up_to : nat -> forall m, terms m -> terms m -> Prop :=
  | teut_nil  : forall n, terms_eq_up_to n Vnil Vnil
  | teut_cons : forall n t u, term_eq_up_to n t u -> 
                forall m (v w : terms m), terms_eq_up_to n v w -> 
                terms_eq_up_to n (Vcons t v) (Vcons u w).

Definition term_eq (t u : term) := 
  forall n, term_eq_up_to n t u.

Definition terms_eq (m : nat) (v w : terms m) := 
  forall n, terms_eq_up_to n v w.

(*
Lemma terms_eq_up_to_0_cast : 
  forall (p : nat) (v : terms p) (q : nat) (w : terms q) (Hqp : q = p), 
  terms_eq_up_to 0 v (vector_cast w Hqp).
Proof.
induction v as [|t p v IH]; intros q w; destruct w as [|u q w]; simpl; intro Hqp.
constructor.
discriminate Hqp.
discriminate Hqp.
constructor.
constructor.
apply IH.
Qed.
*)

Lemma terms_eq_up_to_0 : 
  forall (n : nat) (v w : terms n),
  terms_eq_up_to 0 v w.
Proof.
(*
intros n v w.
rewrite <- (vector_cast_simpl w (refl_equal n)).
apply terms_eq_up_to_0_cast.
(* alternatively ... *)
Restart.
*)
induction v as [|t n v]; dependent destruction w; simpl; constructor.
constructor.
apply IHv.
Qed.

Lemma terms_eq_cons_inv : 
  forall t u n (v w : terms n), 
  terms_eq (Vcons t v) (Vcons u w) ->
  term_eq t u /\ terms_eq v w.
Proof.
intros t u n v w H.
split; intro l; assert (H0 := H l).
inversion_clear H0; assumption.
dependent destruction H0; assumption.
Qed.

Lemma term_bis_implies_term_eq : 
  forall (t u : term), term_bis t u -> term_eq t u.
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

Lemma term_eq_var_inv : forall (x y : X), term_eq (Var x) (Var y) -> x = y.
Proof.
intros x y H.
assert (H0 := H 1).
inversion_clear H0.
reflexivity.
Qed.

Lemma term_eq_fun_inv_symbol : 
  forall (f g : F) (v : terms (arity f)) (w : terms (arity g)),
  term_eq (Fun f v) (Fun g w) -> f = g.
Proof.
intros f g v w H.
assert (H0 := H 1).
inversion_clear H0; simpl.
reflexivity.
Qed.

(*
Lemma term_eq_fun_inv_vec_cast :
  forall (n : nat) (f g : F) (v : terms (arity f)) (w : terms (arity g)),
  term_eq_up_to (S n) (Fun f v) (Fun g w) ->
  forall (Hgf : g = f),
  terms_eq_up_to n v (vector_cast w (f_equal (@arity F) Hgf)).
Proof.
intros n f g v w H Hgf.
dependent destruction H.
rewrite vector_cast_simpl.
exact H.
Qed.
*)

Lemma term_eq_fun_inv_vec :
  forall (f : F) (v w : terms (arity f)),
  term_eq (Fun f v) (Fun f w) ->
  terms_eq v w.
Proof.
intros f v w H n.
assert (H0 := H (S n)).
dependent destruction H0.
assumption.
Qed.

Lemma term_eq_implies_term_bis : forall (t u : term), term_eq t u -> term_bis t u.
Proof.
cofix coIH.
intros [x|f v] [y|g w] H.
rewrite term_eq_var_inv with (1:=H).
constructor.
assert (H0 := H 1); inversion_clear H0.
assert (H0 := H 1); inversion_clear H0.
assert (H0 := sym_eq (term_eq_fun_inv_symbol H)).
dependent destruction H0.
assert (H0 := term_eq_fun_inv_vec H).
apply Fun_bis.
clear H.
induction v as [|t n v]; dependent destruction w. 
constructor.
destruct (terms_eq_cons_inv H0) as [H1 H2].
constructor.
apply coIH; assumption.

(* hier hebben we hetzelfde probleem als met onze corecursieve id-functie:
   de inductie over vectoren (vector_ind) zit tussen de guard (Fun_bis) 
   en de recursieve aanroep (coIH) in. 
   check maar: 
   Guarded.
*)
Abort.

End term_equality.