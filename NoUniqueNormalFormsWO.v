(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library proofs that uniqueness of normal forms (UN) is not implied
   by weak orthogonality (WO) by counterexample. *)


Require Import Rewriting.
Require Import Equality.

Set Implicit Arguments.


(** We construct the weakly orthogonal TRS with rules
    - PS : P(S(x)) -> x
    - SP : S(P(x)) -> x
    and show it is a counterexample to UN-inf.


    J. Endrullis, C. Grabmayer, D. Hendriks, J.W. Klop and V. van Oostrom.
    Unique Normal Forms in Infinitary Weakly Orthogonal Rewriting.
    Rewriting Techniques and Applications, 2010.

    Because we have [S] as constructor for [nat], we rename the function
    symbols to D and U ('up' and 'down').

    Let psi = U D D U U U D D D D... We show that
    - this TRS is weakly orthogonal
    - psi rewrites to DDD...
    - psi rewrites to UUU...
    - DDD... is a normal form
    - UUU... is a normal form
    - DDD... and UUU... are not bisimilar

    Together this gives a counterexample to (WO => UN). *)


(** * Signature

   We have two unary function symbols [D] and [U]. *)

Inductive symbol : Set := D | U.

Definition beq_symb (f g : symbol) : bool :=
  match f, g with
  | D, D => true
  | U, U => true
  | _, _ => false
end.

Lemma beq_symb_ok : forall f g, beq_symb f g = true <-> f = g.
Proof.
(* This should work for any finite inductive symbol type *)
intros f g.
split; intro H.
(* beq_symb f g = true -> f = g *)
  destruct f; destruct g; simpl; (reflexivity || discriminate).
(* f = g ->  beq_symb f g = true *)
  subst g; destruct f; simpl; reflexivity.
Qed.

Definition arity (f : symbol) : nat :=
  match f with
  | D => 1
  | U => 1
  end.

(** * Variables

   We only need one variable that is used in both rewrite rules. *)

Definition variable : Set := unit.

Fixpoint beq_var (x y : variable) : bool := true.

Lemma beq_var_ok : forall x y, beq_var x y = true <-> x = y.
Proof.
intros [] []; split; reflexivity.
Qed.

(** * Terms

   Terms over the given signature and variable. *)

Definition F : signature := Signature arity beq_symb_ok.
Definition X : variables := Variables beq_var_ok.

Notation term := (term F X).
Notation fterm := (finite_term F X).
Notation terms := (vector term).

(** We define notational shortcuts for constructing terms:
   - variable [x] by [x!]
   - function application of [f] to [a] by [f @ a]
   - function application of [f] to [a] by [f @@ a] for finite terms *)

Notation "x !" := (@FVar F X x) (at level 75).

Notation "f @ a" := (@Fun F X f (vcons a (vnil term))) (right associativity, at level 75).
Notation "f @@ a" := (@FFun F X f (vcons a (vnil fterm))) (right associativity, at level 75).

(** UUU... *)
CoFixpoint repeat_U : term :=
  U @ repeat_U.

(** DDD... *)
CoFixpoint repeat_D : term :=
  D @ repeat_D.

(** U^n t *)
Fixpoint Unt (n : nat) t :=
  match n with
  | O   => t
  | S n => U @ (Unt n t)
  end.

(** D^n t *)
Fixpoint Dnt (n : nat) t :=
  match n with
  | O   => t
  | S n => D @ (Dnt n t)
  end.

(** U^2n t *)
Fixpoint U2nt (n : nat) t :=
  match n with
  | O   => t
  | S n => U @ U @ (U2nt n t)
  end.

(** D^2n t *)
Fixpoint D2nt (n : nat) t :=
  match n with
  | O   => t
  | S n => D @ D @ (D2nt n t)
  end.

(** D^n U^n t *)
Definition DnUnt n t : term :=
  Dnt n (Unt n t).

(** U^n D^n t *)
Definition UnDnt n t : term :=
  Unt n (Dnt n t).

(** D^2n U^2n t *)
Definition D2nU2nt n t : term :=
  D2nt n (U2nt n t).

(** U^2n D^2n t *)
Definition U2nD2nt n t : term :=
  U2nt n (D2nt n t).

(** We now define the term

     [psi] = D U^2 D^3 U^4 ...

   via an auxiliary parameterised term [psi'].

   We would like to define psi' like this
[[
     CoFixpoint psi' n : term :=
       Unt n (Dnt (S n) (psi' (S (S n)))).
]]
   but unfortunately this is not in guarded form. We therefore turn to a
   more complex definition with anonymous cofixpoints. *)

(** [psi' n] = D^n U^Sn D^SSn U^SSSn ... *)
CoFixpoint psi' n : term :=
  (cofix D2nDt (d : nat) :=
    match d with
    | O   => D @ (cofix U2nt (u : nat) :=
               match u with
               | O   => psi' (S n)
               | S u => U @ U @ (U2nt u)
               end) (S n)
    | S d => D @ D @ (D2nDt d)
    end) n.

(* [psi] = D U^2 D^3 U^4 ... *)
Definition psi := psi' 0.

(** Some useful lemmas on bisimilarity and equality of common terms follow. *)

Lemma term_bis_U :
  forall t s,
    t [~] s -> (U @ t) [~] (U @ s).
Proof.
intros t s H.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
assumption.
Qed.

Lemma term_bis_D :
  forall t s,
    t [~] s -> (D @ t) [~] (D @ s).
Proof.
intros t s H.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
assumption.
Qed.

Lemma term_eq_up_to_n_Unt_repeat_U :
  forall n t,
    term_eq_up_to n (Unt n t) repeat_U.
Proof.
induction n as [| n IH]; simpl; intro t.
constructor.
rewrite (peek_eq repeat_U); simpl.
constructor.
intro i.
dependent destruction i.
apply IH.
dependent destruction i.
Qed.

Lemma term_eq_up_to_n_Dnt_repeat_D :
  forall n t,
    term_eq_up_to n (Dnt n t) repeat_D.
Proof.
induction n as [| n IH]; simpl; intro t.
constructor.
rewrite (peek_eq repeat_D); simpl.
constructor.
intro i.
dependent destruction i.
apply IH.
dependent destruction i.
Qed.

Lemma term_bis_Unt :
  forall n t s,
    t [~] s -> Unt n t [~] Unt n s.
Proof.
induction n; intros t s H; simpl.
assumption.
apply term_bis_U.
apply IHn.
assumption.
Qed.

Lemma term_bis_Dnt :
  forall n t s,
    t [~] s -> Dnt n t [~] Dnt n s.
Proof.
induction n; intros t s H; simpl.
assumption.
apply term_bis_D.
apply IHn.
assumption.
Qed.

Lemma UUnt_eq_UnUt :
  forall n t,
    (U @ Unt n t) = Unt n (U @ t).
induction n; intro t.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Lemma DDnt_eq_DnDt :
  forall n t,
    (D @ Dnt n t) = Dnt n (D @ t).
induction n; intro t.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Lemma UU2nt_eq_U2nUt :
  forall n t,
    (U @ U2nt n t) = U2nt n (U @ t).
induction n; intro t.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Lemma DD2nt_eq_D2nDt :
  forall n t,
    (D @ D2nt n t) = D2nt n (D @ t).
induction n; intro t.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Lemma DSnUSnt_eq_DDnUnUt :
  forall n t,
    DnUnt (S n) t = (D @ (DnUnt n (U @ t))).
Proof.
intros n t.
unfold DnUnt.
simpl.
rewrite UUnt_eq_UnUt.
reflexivity.
Qed.

Lemma USnDSnt_eq_UUnDnDt :
  forall n t,
    UnDnt (S n) t = (U @ (UnDnt n (D @ t))).
Proof.
intros n t.
unfold UnDnt.
simpl.
rewrite DDnt_eq_DnDt.
reflexivity.
Qed.

Lemma D2SnU2Snt_eq_DDD2nU2nUUt :
  forall n t,
    D2nU2nt (S n) t = (D @ D @ (D2nU2nt n (U @ U @ t))).
Proof.
intros n t.
unfold D2nU2nt.
simpl.
rewrite UU2nt_eq_U2nUt.
rewrite UU2nt_eq_U2nUt.
reflexivity.
Qed.

Lemma U2SnD2Snt_eq_UUU2nD2nDDt :
  forall n t,
    U2nD2nt (S n) t = (U @ U @ (U2nD2nt n (D @ D @ t))).
Proof.
intros n t.
unfold U2nD2nt.
simpl.
rewrite DD2nt_eq_D2nDt.
rewrite DD2nt_eq_D2nDt.
reflexivity.
Qed.

Lemma D2nU2nt_eq_D2nU2nt :
  forall n t,
    D2nU2nt n t = DnUnt (2 * n) t.
Proof.
induction n; intro t; simpl.
unfold D2nU2nt, D2nt, U2nt, DnUnt, Dnt, Unt.
reflexivity.
rewrite D2SnU2Snt_eq_DDD2nU2nUUt.
rewrite DSnUSnt_eq_DDnUnUt.
rewrite IHn with (U @ U @ t).
simpl.
rewrite (eq_sym (plus_n_Sm n (n + 0))).
rewrite DSnUSnt_eq_DDnUnUt.
reflexivity.
Qed.

(** Some useful (but ugly) lemmas on bisimilarity and equality of psi and
   (partial) unfoldings follow. *)

Lemma UU2nt_eq_U2nUt_unfolded :
  forall n t,
    (U @ (cofix U2nt (u : nat) : term :=
            match u with
            | 0 => t
            | S u0 => U @ U @ U2nt u0
            end) n)
    =
    (cofix U2nt (u : nat) : term :=
       match u with
       | 0 => U @ t
       | S u0 => U @ U @ U2nt u0
       end) n.
Proof.
induction n; intro t.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
        match u with
        | 0 => t
        | S u0 => U @ U @ U2nt u0
        end) 0)).
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ U @ U2nt u0
      end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) (S n))).
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ U @ U2nt u0
      end) (S n))).
simpl.
rewrite IHn with t.
reflexivity.
Qed.

Lemma psin_eq_DD2nU2nUUpsiSn :
  forall n,
    psi' n = (D @ (D2nU2nt n (U @ U @ (psi' (S n))))).
Proof.
intro n.
rewrite (peek_eq (psi' n)).
simpl.
generalize (psi' (S n)).
induction n; intro t.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) 1)).
unfold D2nU2nt.
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
                 match u with
                 | 0 => t
                 | S u0 => U @ U @ U2nt u0
                 end) (S (S n)))).
rewrite D2SnU2Snt_eq_DDD2nU2nUUt.
simpl.
rewrite UU2nt_eq_U2nUt_unfolded with (S n) t.
rewrite UU2nt_eq_U2nUt_unfolded with (S n) (U @ t).
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
       match d with
       | 0 =>
           D @
           (cofix U2nt (u : nat) : term :=
              match u with
              | 0 => U @ U @ t
              | S u0 => U @ U @ U2nt u0
              end) (S n)
       | S d0 => D @ D @ D2nDt d0
       end) n)).
simpl.
rewrite IHn with (U @ U @ t).
reflexivity.
Qed.

Lemma psin_eq_DS2nUS2nUpsiSn :
  forall n,
    psi' n = DnUnt (S (2 * n)) (U @ (psi' (S n))).
Proof.
intro n.
rewrite psin_eq_DD2nU2nUUpsiSn.
rewrite D2nU2nt_eq_D2nU2nt.
rewrite DSnUSnt_eq_DDnUnUt.
reflexivity.
Qed.

(** * Contexts

   Contexts over the given signature and variable. *)

Notation context := (context F X).

(** Notational shortcut for function application in contexts. *)
Notation "f @@@ a" := (@CFun F X f 0 0 (@refl_equal nat (arity f)) (vnil term) a (vnil term)) (right associativity, at level 75).

(** D^n c *)
Fixpoint Dnc n c : context :=
  match n with
  | O   => c
  | S n => D @@@ (Dnc n c)
  end.

(** U^n c *)
Fixpoint Unc n c : context :=
  match n with
  | O   => c
  | S n => U @@@ (Unc n c)
  end.

(** We prove some lemmas about filling contexts. *)

Lemma fill_Dnc_t :
  forall n c t,
    fill (Dnc n c) t = Dnt n (fill c t).
Proof.
induction n.
reflexivity.
intros c t.
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma fill_Unc_t :
  forall n c t,
    fill (Unc n c) t = Unt n (fill c t).
Proof.
induction n.
reflexivity.
intros c t.
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma fill_DnHole_t :
  forall n t,
    fill (Dnc n Hole) t = Dnt n t.
Proof.
intros n t.
apply fill_Dnc_t.
Qed.

Lemma fill_UnHole_t :
  forall n t,
    fill (Unc n Hole) t = Unt n t.
Proof.
intros n t.
apply fill_Unc_t.
Qed.

Lemma fill_DmUnc_t :
  forall m n c t,
    fill (Dnc m (Unc n c)) t = Dnt m (Unt n (fill c t)).
Proof.
intros m n c t.
rewrite fill_Dnc_t.
rewrite fill_Unc_t.
reflexivity.
Qed.

Lemma fill_UmDnc_t :
  forall m n c t,
    fill (Unc m (Dnc n c)) t = Unt m (Dnt n (fill c t)).
Proof.
intros m n c t.
rewrite fill_Unc_t.
rewrite fill_Dnc_t.
reflexivity.
Qed.

Lemma fill_DmUnHole_t :
  forall m n t,
    fill (Dnc m (Unc n Hole)) t = Dnt m (Unt n t).
Proof.
intros m n t.
apply fill_DmUnc_t.
Qed.

Lemma fill_UmDnHole_t :
  forall m n t,
    fill (Unc m (Dnc n Hole)) t = Unt m (Dnt n t).
Proof.
intros m n t.
apply fill_UmDnc_t.
Qed.

(** * Rewriting

   We construct the rewrite rules for the TRS and show it is weakly
   orthogonal. We also show that UUU... and DDD... are normal forms. *)

Notation trs := (trs F X).

(** We use this variable in the rewrite rules *)
Definition varx : X := tt.

(** Rule [DU] : DUx -> x *)

Definition DU_l : fterm := D @@ U @@ varx!.
Definition DU_r : fterm := varx!.

Lemma wf_DU :
  is_var DU_l = false /\
  incl (vars DU_r) (vars DU_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition DU : rule := Rule DU_l DU_r wf_DU.

(** Rule [UD] : UDx -> x *)

Definition UD_l : fterm := U @@ D @@ varx!.
Definition UD_r : fterm := varx!.

Lemma wf_UD :
  is_var UD_l = false /\
  incl (vars UD_r) (vars UD_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition UD : rule := Rule UD_l UD_r wf_UD.

(** The TRS [UD_trs] as a list of its rules. *)

Definition UD_trs : trs := DU :: UD :: nil.

(** [UD_trs] is trivialy left-linear. *)
Lemma left_linear_UD :
  trs_left_linear UD_trs.
Proof.
constructor; [| constructor];
  unfold left_linear; unfold linear; simpl;
    constructor.
intro; assumption.
constructor.
intro; assumption.
constructor.
Qed.

(** All critical pairs in [UD_trs] are trivial. *)
Lemma critical_pairs_trivial_UD :
  forall t1 t2,
    critical_pair UD_trs t1 t2 ->
    t1 [~] t2.
Proof.
intros t1 t2 H.
unfold critical_pair in H.
destruct H as [r1 [r2 [[| [| a] [| [| b] [| c p]]] [sigma [tau [[Hr1 | [Hr1 | []]] [[Hr2 | [Hr2 | []]] [T H]]]]]]]];
rewrite <- Hr1 in * |-;
rewrite <- Hr2 in * |-;
clear r1 r2 Hr1 Hr2;
try (contradict T; auto; fail);
clear T;
try (contradict H; fail); simpl in H;
destruct H as [V [H [H1 H2]]];
try (contradict V; fail);
apply (term_bis_trans H1); apply term_bis_symm; apply (term_bis_trans H2);
clear H1 H2;
dependent destruction H; specialize H with (First (n := 0)); unfold vmap in H; simpl in H;
dependent destruction H; specialize H with (First (n := 0)); unfold vmap in H; simpl in H;
clear V.

rewrite <- x.
constructor.
intro i.
dependent destruction i.
unfold vcast.
generalize (lt_plus_minus_r (Gt.gt_le_S 0 1 (Lt.lt_0_Sn 0))).
intro e.
dependent destruction e.
generalize (lt_plus_minus_r (Lt.lt_le_S 0 1 (Lt.lt_0_Sn 0))).
intro e.
dependent destruction e.
assumption.
inversion i.

rewrite <- x.
constructor.
intro i.
dependent destruction i.
unfold vcast.
generalize (lt_plus_minus_r (Gt.gt_le_S 0 1 (Lt.lt_0_Sn 0))).
intro e.
dependent destruction e.
generalize (lt_plus_minus_r (Lt.lt_le_S 0 1 (Lt.lt_0_Sn 0))).
intro e.
dependent destruction e.
assumption.
inversion i.
Qed.

Lemma weakly_orthogonal_UD :
  weakly_orthogonal UD_trs.
Proof.
split.
exact left_linear_UD.
exact critical_pairs_trivial_UD.
Qed.

(** DDD... is a normal form. *)
Lemma normal_form_repeat_D :
  normal_form UD_trs repeat_D.
Proof.
(** TODO: a lot of this proof is a mess, cleanup.
   Also, I expect that this could be generalized and shortened quite a bit
   by using pos_eq. *)
intros [c [r [u [H1 H2]]]].
destruct H1 as [H1 | [H1 | []]].
rewrite <- H1 in *|-.
clear H1.
assert (H := (term_bis_implies_term_eq H2) (S (S (hole_depth c)))).
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
assert (H' := H First).
rewrite (peek_eq repeat_D) in H'.
dependent destruction H'.
assert (H' := H0 First).
simpl in H'.

(* idea, make [=]1 from x0 *)
assert (y0 : term_eq_up_to 1 (@Fun F X D v) (fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ varx!) (vnil fterm)))))).
(*assert (y0 : @Fun F X D v [=] fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm))))).*)
rewrite x0.
apply term_eq_up_to_refl.
clear x0.

induction c.

assert (H3 := (term_bis_implies_term_eq H2) 2).
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.
assert (H3 := H1 First).
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.

rewrite (peek_eq repeat_D) in H2.
(*intro x0.*)
assert (d : f = D).
(*assert (y1 := y0 1).*)
inversion_clear y0.
reflexivity.

(*injection x0.
intros _ d.*)
revert e H2 H y0 H0 H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v1 v2.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H y0 H0 H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
apply term_eq_implies_term_bis.
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X D (vcons (fill c (substitute u (lhs DU))) v2)) (D @ repeat_D)).
assert (jaja : fill (@CFun F X D 0 0 e v1 c v2) (substitute u (lhs DU)) = @Fun F X D (vcons (fill c (substitute u (lhs DU))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact ((term_bis_implies_term_eq H2) (S n)).
apply (@teut_fun_inv F X n D (vcons (fill c (substitute u (lhs DU))) v2) (vcons repeat_D (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
intro i.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.

clear v0 x H y0 H0 H'.
destruct c.
constructor.
constructor.
simpl.
simpl in H2.
dependent destruction H2.
assert (H3 := H First).
simpl in H3.
clear H.
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.
revert x.
dependent destruction e.
intro y.
simpl in y.
injection y.
intros _ d.
clear y x H v1 v2 v4.
revert e0.
rewrite <- d.
intro e.
constructor.
constructor.

(** Almost the same argument follows for [r=UD] instead of [r=DU]. *)

rewrite <- H1 in *|-.
clear H1.
assert (H := (term_bis_implies_term_eq H2) (S (hole_depth c))).
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
assert (H' := H First).
simpl in H'.
clear x.

induction c.

rewrite (peek_eq repeat_D) in H2.
inversion_clear H2.

rewrite (peek_eq repeat_D) in H2.
(*intro x0.*)
assert (d : f = D).
inversion_clear H2.
reflexivity.

revert e H2 H H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v0 v1.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
apply term_eq_implies_term_bis.
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X D (vcons (fill c (substitute u (lhs UD))) v2)) (D @ repeat_D)).
assert (jaja : fill (@CFun F X D 0 0 e v1 c v2) (substitute u (lhs UD)) = @Fun F X D (vcons (fill c (substitute u (lhs UD))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact ((term_bis_implies_term_eq H2) (S n)).
apply (@teut_fun_inv F X n D (vcons (fill c (substitute u (lhs UD))) v2) (vcons repeat_D (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
apply term_eq_up_to_weaken.
assumption.
Qed.

(** UUU... is a normal form. *)
Lemma normal_form_repeat_U :
  normal_form UD_trs repeat_U.
Proof.
(** This proof is just a copy of the DDD... proof. *)
intros [c [r [u [H1 H2]]]].
destruct H1 as [H1 | [H1 | []]].

rewrite <- H1 in *|-.
clear H1.
assert (H := (term_bis_implies_term_eq H2) (S (hole_depth c))).
rewrite (peek_eq repeat_U) in H.
dependent destruction H.
assert (H' := H First).
simpl in H'.
clear x.

induction c.

rewrite (peek_eq repeat_U) in H2.
inversion_clear H2.

rewrite (peek_eq repeat_U) in H2.
(*intro x0.*)
assert (d : f = U).
inversion_clear H2.
reflexivity.

revert e H2 H H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v0 v1.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
apply term_eq_implies_term_bis.
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X U (vcons (fill c (substitute u (lhs DU))) v2)) (U @ repeat_U)).
assert (jaja : fill (@CFun F X U 0 0 e v1 c v2) (substitute u (lhs DU)) = @Fun F X U (vcons (fill c (substitute u (lhs DU))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact ((term_bis_implies_term_eq H2) (S n)).
apply (@teut_fun_inv F X n U (vcons (fill c (substitute u (lhs DU))) v2) (vcons repeat_U (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
apply term_eq_up_to_weaken.
assumption.

(** Almost the same argument follows for [r=UD] instead of [r=DU]. *)

rewrite <- H1 in *|-.
clear H1.
assert (H := (term_bis_implies_term_eq H2) (S (S (hole_depth c)))).
rewrite (peek_eq repeat_U) in H.
dependent destruction H.
assert (H' := H First).
rewrite (peek_eq repeat_U) in H'.
dependent destruction H'.
assert (H' := H0 First).
simpl in H'.

(* idea, make [=]1 from x0 *)
assert (y0 : term_eq_up_to 1 (@Fun F X U v) (fill c (@Fun F X U (vmap (substitute u) (vcons (D @@ varx!) (vnil fterm)))))).
(*assert (y0 : @Fun F X D v [=] fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm))))).*)
rewrite x0.
apply term_eq_up_to_refl.
clear x0.

induction c.

assert (H3 := (term_bis_implies_term_eq H2) 2).
rewrite (peek_eq repeat_U) in H3.
dependent destruction H3.
assert (H3 := H1 First).
rewrite (peek_eq repeat_U) in H3.
dependent destruction H3.

rewrite (peek_eq repeat_U) in H2.
(*intro x0.*)
assert (d : f = U).
(*assert (y1 := y0 1).*)
inversion_clear y0.
reflexivity.

(*injection x0.
intros _ d.*)
revert e H2 H y0 H0 H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v1 v2.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H y0 H0 H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
apply term_eq_implies_term_bis.
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X U (vcons (fill c (substitute u (lhs UD))) v2)) (U @ repeat_U)).
assert (jaja : fill (@CFun F X U 0 0 e v1 c v2) (substitute u (lhs UD)) = @Fun F X U (vcons (fill c (substitute u (lhs UD))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact ((term_bis_implies_term_eq H2) (S n)).
apply (@teut_fun_inv F X n U (vcons (fill c (substitute u (lhs UD))) v2) (vcons repeat_U (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
intro i.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.

clear v0 x H y0 H0 H'.
destruct c.
constructor.
constructor.
simpl.
simpl in H2.
dependent destruction H2.
assert (H3 := H First).
simpl in H3.
clear H.
rewrite (peek_eq repeat_U) in H3.
dependent destruction H3.
revert x.
dependent destruction e.
intro y.
simpl in y.
injection y.
intros _ d.
clear y x H v1 v2 v4.
revert e0.
rewrite <- d.
intro e.
constructor.
constructor.
Qed.

(** DDD... and UUU... are different. *)
Lemma neq_repeat_D_repeat_U :
  ~ repeat_D [~] repeat_U.
Proof.
intro H.
rewrite (peek_eq repeat_D), (peek_eq repeat_U) in H.
inversion H.
Qed.

(** * Rewrite sequences

   We now build our infinite rewrite sequences. *)

Notation Step := (Step UD_trs).
Notation Nil' := (Nil UD_trs).

Notation "s [>] t" := (step UD_trs s t) (at level 40).
Notation "s ->> t" := (sequence UD_trs s t) (at level 40).

Notation "r [ i ]" := (pred r i) (at level 60).
Notation "r [1 i ]" := (fst (projT1 (pred r i))) (at level 60).
Notation "r [2 i ]" := (snd (projT1 (pred r i))) (at level 60).
Notation "r [seq i ]" := (fst (projT2 (pred r i))) (at level 60).
Notation "r [stp i ]" := (snd (projT2 (pred r i))) (at level 60).

Lemma DU_in :
  In DU UD_trs.
Proof.
left; reflexivity.
Qed.

Lemma UD_in :
  In UD UD_trs.
Proof.
right; left; reflexivity.
Qed.

Definition sub_t t (x : X) : term := t.

(** ** psi ->> UUU... *)

Lemma fact_term_bis_UmDSnUSnt :
  forall (m n : nat) (t : term),
    fill (Unc m (Dnc n Hole)) (substitute (sub_t (Unt n t)) (lhs DU))
    [~]
    Unt m (DnUnt (S n) t).
Proof.
intros m n t.
rewrite fill_UmDnHole_t.
unfold DnUnt.
simpl.
rewrite DDnt_eq_DnDt.
apply term_bis_Unt.
apply term_bis_Dnt.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
apply term_bis_refl.
Qed.

Lemma fact_term_eq_UmDnUnt :
  forall (m n : nat) (t : term),
    fill (Unc m (Dnc n Hole)) (substitute (sub_t (Unt n t)) (rhs DU))
    =
    Unt m (DnUnt n t).
Proof.
intros m n t.
rewrite fill_Unc_t.
rewrite fill_Dnc_t.
simpl.
reflexivity.
Qed.

Lemma fact_term_bis_UmDnUnt :
  forall (m n : nat) (t : term),
    fill (Unc m (Dnc n Hole)) (substitute (sub_t (Unt n t)) (rhs DU))
    [~]
    Unt m (DnUnt n t).
Proof.
intros m n t.
rewrite fact_term_eq_UmDnUnt.
apply term_bis_refl.
Qed.

(** Step from U^m D^Sn U^Sn to U^m D^n U^n t. *)
Definition p_UmDSnUSnt_UmDnUnt m n t : Unt m (DnUnt (S n) t) [>] Unt m (DnUnt n t) :=
  Step DU (Unc m (Dnc n Hole)) (sub_t (Unt n t)) DU_in (fact_term_bis_UmDSnUSnt m n t) (fact_term_bis_UmDnUnt m n t).

(** n-step rewrite sequence from U^m D^n U^n t to U^m t. *)
Fixpoint s_UmDnUnt_Umt m n t : Unt m (DnUnt n t) ->> Unt m t :=
  match n return Unt m (DnUnt n t) ->> Unt m t with
  | O   => Nil' (Unt m t)
  | S n => snoc (p_UmDSnUSnt_UmDnUnt m n t) (s_UmDnUnt_Umt m n t)
  end.

(** 2n+1-step rewrite sequence from U^n [psi' n] to U^Sn [psi' Sn]. *)
Definition s_Unpsin_USnpsiSn n : Unt n (psi' n) ->> Unt (S n) (psi' (S n)).
(** Coq 8.3-rc1 does the 'intro n' automatically, but 8.3-beta0-1 needs it. *)
intros.
assert (H : Unt n (DnUnt (S (2 * n)) (U @ psi' (S n))) ->> Unt n (U @ psi' (S n))).
refine (s_UmDnUnt_Umt n (S (2 * n)) (U @ psi' (S n))).
unfold DnUnt in H.
rewrite psin_eq_DS2nUS2nUpsiSn.
simpl.
simpl in H.
unfold DnUnt.
simpl.
rewrite UUnt_eq_UnUt with n (psi' (S n)).
exact H.
Defined.

(** We would have liked to define the above by the following definition
   using [Program], but unfortunately it is not accepted by Coq. Is this
   a bug in [Program]?

[[
Program Definition s_Unpsin_USnpsiSn n : Unt n (psi' n) ->> Unt (S n) (psi' (S n)) :=
  s_UmDnUnt_Umt n (S (2 * n)) (U @ psi' (S n)).
Next Obligation.
symmetry.
unfold DnUnt.
rewrite psin_eq_DS2nUS2nUpsiSn.
reflexivity.
Defined.
Next Obligation.
rewrite UUnt_eq_UnUt.
reflexivity.
Defined.
]]
*)

(** Rewrite sequence from [psi] to U^n [psi' n]. *)
Fixpoint s_psi_Unpsin n : psi ->> Unt n (psi' n) :=
  match n return psi ->> Unt n (psi' n) with
  | O   => Nil' psi
  | S n => append (s_psi_Unpsin n) (s_Unpsin_USnpsiSn n)
  end.

Lemma converges_Unpsin : converges (fun n => Unt n (psi' n)) repeat_U.
Proof.
intro d.
exists d.
intros m H.
simpl.
apply term_eq_up_to_weaken_generalized with m.
assumption.
apply term_eq_up_to_n_Unt_repeat_U.
Qed.

(** Omega-step rewrite sequence from [psi] to UUU... *)
Definition s_psi_repeat_U : psi ->> repeat_U :=
  Lim s_psi_Unpsin converges_Unpsin.

(** ** psi ->> DDD... *)

Lemma fact_term_bis_DmUSnDSnt :
  forall (m n : nat) (t : term),
    fill (Dnc m (Unc n Hole)) (substitute (sub_t (Dnt n t)) (lhs UD))
    [~]
    Dnt m (UnDnt (S n) t).
Proof.
intros m n t.
rewrite fill_DmUnHole_t.
unfold UnDnt.
simpl.
rewrite UUnt_eq_UnUt.
apply term_bis_Dnt.
apply term_bis_Unt.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
apply term_bis_refl.
Qed.

Lemma fact_term_eq_DmUnDnt :
  forall (m n : nat) (t : term),
    fill (Dnc m (Unc n Hole)) (substitute (sub_t (Dnt n t)) (rhs UD))
    =
    Dnt m (UnDnt n t).
Proof.
intros m n t.
rewrite fill_Dnc_t.
rewrite fill_Unc_t.
simpl.
reflexivity.
Qed.

Lemma fact_term_bis_DmUnDnt :
  forall (m n : nat) (t : term),
    fill (Dnc m (Unc n Hole)) (substitute (sub_t (Dnt n t)) (rhs UD))
    [~]
    Dnt m (UnDnt n t).
Proof.
intros m n t.
rewrite fact_term_eq_DmUnDnt.
apply term_bis_refl.
Qed.

(* Step from D^m U^Sn D^Sn t to D^m U^n D^n t. *)
Definition p_DmUSnDSnt_DmUnDnt m n t : Dnt m (UnDnt (S n) t) [>] Dnt m (UnDnt n t) :=
  Step UD (Dnc m (Unc n Hole)) (sub_t (Dnt n t)) UD_in (fact_term_bis_DmUSnDSnt m n t) (fact_term_bis_DmUnDnt m n t).

(* n-step rewrite sequence from D^m U^n D^n t to D^m t. *)
Fixpoint s_DmUnDnt_Dmt m n t : Dnt m (UnDnt n t) ->> Dnt m t :=
  match n return Dnt m (UnDnt n t) ->> Dnt m t with
  | O   => Nil' (Dnt m t)
  | S n => snoc (p_DmUSnDSnt_DmUnDnt m n t) (s_DmUnDnt_Dmt m n t)
  end.

(** 2n-step rewrite sequence from D^n U^2n [psi' n] to D^Sn U2Sn [psi' Sn]. *)
Definition s_DnU2npsin_DSnU2SnpsiSn n : Dnt n (Unt (2 * n) (psi' n)) ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n))).
(** Coq 8.3-rc1 does the 'intro n' automatically, but 8.3-beta0-1 needs it. *)
intros.
assert (H : Dnt n (UnDnt (2 * n) (D @ Unt (2 * (S n)) (psi' (S n)))) ->> Dnt n (D @ (Unt (2 * S n)) (psi' (S n)))).
refine (s_DmUnDnt_Dmt n (2 * n) (D @ (Unt (2 * (S n)) (psi' (S n))))).
unfold UnDnt in H.
rewrite psin_eq_DS2nUS2nUpsiSn.
unfold DnUnt.
simpl.
rewrite DDnt_eq_DnDt.
simpl in H.
rewrite <- plus_n_Sm in H.
rewrite <- plus_n_Sm.
simpl in H.
simpl.
rewrite <- UUnt_eq_UnUt.
rewrite DDnt_eq_DnDt.
exact H.
Defined.

(** We would have liked to define the above by the following definition
   using [Program], but unfortunately it is not accepted by Coq. Is this
   a bug in [Program]?

[[
Program Definition s_DnU2npsin_DSnU2SnpsiSn n : Dnt n (Unt (2 * n) (psi' n)) ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n))) :=
  s_DmUnDnt_Dmt n (2 * n) (D @ (Unt (2 * (S n)) (psi' (S n)))).
Next Obligation.
symmetry.
unfold UnDnt.
rewrite psin_eq_DS2nUS2nUpsiSn.
unfold DnUnt.
simpl.
rewrite DDnt_eq_DnDt.
rewrite <- plus_n_Sm.
rewrite <- UUnt_eq_UnUt.
reflexivity.
Defined.
Next Obligation.
rewrite DDnt_eq_DnDt.
reflexivity.
Defined.
]]
*)

(** Rewrite sequence from [psi] to D^Sn U^2Sn [psi' Sn]. *)
Fixpoint s_psi_DSnU2SnpsiSn n : psi ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n))) :=
  match n return psi ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n))) with
  | O   => s_DnU2npsin_DSnU2SnpsiSn 0
  | S n => append (s_psi_DSnU2SnpsiSn n) (s_DnU2npsin_DSnU2SnpsiSn (S n))
  end.

Lemma converges_DSnU2SnpsiSn : converges (fun n => Dnt (S n) (Unt (2 * (S n)) (psi' (S n)))) repeat_D.
Proof.
intro d.
exists d.
intros m H.
simpl.
apply term_eq_up_to_weaken_generalized with m.
assumption.
rewrite DDnt_eq_DnDt.
apply term_eq_up_to_n_Dnt_repeat_D.
Qed.

(* Omega-step reduction from [psi] to DDD... *)
Definition s_psi_repeat_D : psi ->> repeat_D :=
  Lim s_psi_DSnU2SnpsiSn converges_DSnU2SnpsiSn.

(** * Well-formedness of the rewrite sequences

   It should be noted that at this point, nothing has been said yet about
   well-formedness of the two rewrite sequences. Furthermore, they might
   not be convergent.

   So we proceed by proving the [wf] property for the rewrite sequences.
   Convergence seems our of our reach at this point unfortunately. *)

(** ** Well-formedness of psi ->> UUU...

   We first prove all finite prefixes are indeed finite. Then we prove that
   every branch of the [Lim] constructor is embedded in the next branch. *)

Lemma finite_s_UmDnUnt_Umt :
  forall m n t, finite (s_UmDnUnt_Umt m n t).
Proof.
induction n as [| n IH]; intro t; simpl.
exact I.
apply snoc_finite.
apply IH.
Qed.

Lemma finite_s_Unpsin_USnpsiSn :
  forall n, finite (s_Unpsin_USnpsiSn n).
Proof.
intro n.
unfold s_Unpsin_USnpsiSn; simpl.
unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
apply finite_s_UmDnUnt_Umt.
Qed.

Lemma finite_s_psi_Unpsin :
  forall n : nat, finite (s_psi_Unpsin n).
Proof.
induction n as [| n IH]; simpl.
exact I.
apply append_finite.
exact IH.
apply finite_s_Unpsin_USnpsiSn.
Qed.

(** The following lemmas help establish [wf]. They are not pretty. *)

Lemma s_UmDnUnt_Umt_is_cons :
  forall m n t,
    exists s, exists r : _ ->> s, exists p : s [>] _,
      s_UmDnUnt_Umt m (S n) t = Cons r p.
Proof.
induction n; intro t; simpl.
exists (Unt m (DnUnt 1 t)).
exists (Nil' (Unt m (DnUnt 1 t))).
exists (p_UmDSnUSnt_UmDnUnt m 0 t).
reflexivity.
simpl in IHn.
specialize IHn with t.
destruct IHn as [s [r [p IH]]].
rewrite IH.
simpl.
exists s.
exists (snoc (p_UmDSnUSnt_UmDnUnt m (S n) t) r).
exists p.
reflexivity.
Qed.

Lemma embed_strict_append_Unpsin_USnpsiSn :
  forall t n (r : t ->> Unt n (psi' n)),
    embed_strict r (append r (s_Unpsin_USnpsiSn n)).
Proof.
intro t.
destruct n as [| n]; simpl;
unfold s_Unpsin_USnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl); intro r.
exists (inl _ tt).
apply embed_refl.
revert r.
rewrite <- (plus_n_Sm n).
rewrite <- plus_n_O.
intro r.
destruct (s_UmDnUnt_Umt_is_cons (S n) (n + n) (U @ psi' (S (S n)))) as [s [q [p H]]].
rewrite H.
exists (inl _ tt).
simpl.
apply embed_append_right.
Qed.

Lemma wf_s_psi_Unpsin :
  forall n : nat, wf (s_psi_Unpsin n).
Proof.
intro n.
apply wf_finite.
apply finite_s_psi_Unpsin.
Qed.

Lemma wf_s_psi_repeat_U :
  wf s_psi_repeat_U.
Proof.
split.
apply wf_s_psi_Unpsin.
intros n m H.
induction H; simpl.
apply embed_strict_append_Unpsin_USnpsiSn.
apply embed_strict_trans with psi (Unt m (psi' m)) (s_psi_Unpsin m).
apply IHle.
apply embed_strict_append_Unpsin_USnpsiSn.
Qed.

(** ** Well-formedness of psi ->> DDD...

   We first prove all finite prefixes are indeed finite. Then we prove that
   every branch of the [Lim] constructor is embedded in the next branch. *)

Lemma finite_s_DmUnDnt_Dmt :
  forall m n t, finite (s_DmUnDnt_Dmt m n t).
Proof.
induction n as [| n IH]; intro t; simpl.
exact I.
apply snoc_finite.
apply IH.
Qed.

(** It is very unclear to me why we have to take this statement apart. *)
Lemma finite_s_DnU2npsin_DSnU2SnpsiSn_helper :
  forall n,
       finite
     (eq_rect
        (Dnt (n + (n + 0)) (D @ U @ Unt (n + (n + 0)) (U @ psi' (S n))))
        (fun y : term =>
         Dnt n (Unt (n + (n + 0)) y) ->>
         Dnt n (D @ U @ U @ Unt (n + (n + 0)) (psi' (S n))))
        (eq_rect (U @ Unt (n + (n + 0)) (psi' (S n)))
           (fun t : term =>
            Dnt n (Unt (n + (n + 0)) (Dnt (n + (n + 0)) (D @ U @ t))) ->>
            Dnt n (D @ U @ U @ Unt (n + (n + 0)) (psi' (S n))))
           (s_DmUnDnt_Dmt n (n + (n + 0))
              (D @ U @ U @ Unt (n + (n + 0)) (psi' (S n))))
           (Unt (n + (n + 0)) (U @ psi' (S n)))
           (UUnt_eq_UnUt (n + (n + 0)) (psi' (S n))))
        (D @ Dnt (n + (n + 0)) (U @ Unt (n + (n + 0)) (U @ psi' (S n))))
        (eq_sym
           (DDnt_eq_DnDt (n + (n + 0))
              (U @ Unt (n + (n + 0)) (U @ psi' (S n)))))).
Proof.
intro n.
repeat (elim_eq_rect ; simpl).
apply finite_s_DmUnDnt_Dmt.
Qed.

Lemma finite_s_DnU2npsin_DSnU2SnpsiSn :
  forall n, finite (s_DnU2npsin_DSnU2SnpsiSn n).
Proof.
intro n.
unfold s_DnU2npsin_DSnU2SnpsiSn; simpl.
unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
apply finite_s_DnU2npsin_DSnU2SnpsiSn_helper.
Qed.

(** It is very unclear to me why we have to take this statement apart. *)
Lemma finite_s_psi_DSnU2SnpsiSn_helper :
   finite
     (eq_rect (DnUnt 1 (U @ psi' 1))
        (fun y : term => y ->> (D @ U @ U @ psi' 1))
        (Nil' (D @ U @ U @ psi' 1)) (psi' 0) (eq_sym (psin_eq_DS2nUS2nUpsiSn 0))).
Proof.
elim_eq_rect; simpl.
exact I.
Qed.

Lemma finite_s_psi_DSnU2SnpsiSn :
  forall n : nat, finite (s_psi_DSnU2SnpsiSn n).
Proof.
induction n as [| n IH]; simpl.
unfold s_DnU2npsin_DSnU2SnpsiSn; simpl.
unfold eq_rect_r; repeat (elim_eq_rect; simpl).
apply finite_s_psi_DSnU2SnpsiSn_helper.
apply append_finite.
exact IH.
exact (finite_s_DnU2npsin_DSnU2SnpsiSn (S n)).
Qed.

(** We use this predicate and the following lemmas to prove well-formedness.
   Yes, this is ugly and a bit of a hack. *)
Fixpoint is_cons s t (r : s ->> t) : Prop :=
  match r with
  | Nil _          => False
  | Cons _ _ q _ _ => True
  | Lim _ _ f t c  => False
  end.

Lemma is_cons_snoc :
  forall s t u (p : s [>] t) (r : t ->> u),
    is_cons r ->
    is_cons (snoc p r).
Proof.
intros.
destruct r; simpl.
exact I.
exact I.
inversion H.
Qed.

Lemma append_is_cons :
  forall s t u (r : s ->> t) (q : t ->> u),
    is_cons q ->
    embed_strict r (append r q).
Proof.
intros.
destruct q.
elim H.
simpl.
exists (inl _ tt).
simpl.
apply embed_append_right.
elim H.
Qed.

Lemma is_cons_s_DmUnDnt_Dmt :
  forall m n t, is_cons (s_DmUnDnt_Dmt m (S n) t).
Proof.
induction n as [| n IH]; intro t; simpl.
exact I.
apply is_cons_snoc.
apply IH.
Qed.

(** It is very unclear to me why we have to take this statement apart. *)
Lemma is_cons_s_DnU2npsin_DSnU2SnpsiSn_helper :
  forall n,
   is_cons
     (eq_rect
        (Dnt (S n + (S n + 0))
           (D @ U @ Unt (S n + (S n + 0)) (U @ psi' (S (S n)))))
        (fun y : term =>
         Dnt (S n) (Unt (S n + (S n + 0)) y) ->>
         Dnt (S n) (D @ U @ U @ Unt (S n + (S n + 0)) (psi' (S (S n)))))
        (eq_rect (U @ Unt (S n + (S n + 0)) (psi' (S (S n))))
           (fun t : term =>
            Dnt (S n)
              (Unt (S n + (S n + 0)) (Dnt (S n + (S n + 0)) (D @ U @ t))) ->>
            Dnt (S n) (D @ U @ U @ Unt (S n + (S n + 0)) (psi' (S (S n)))))
           (s_DmUnDnt_Dmt (S n) (S n + (S n + 0))
              (D @ U @ U @ Unt (S n + (S n + 0)) (psi' (S (S n)))))
           (Unt (S n + (S n + 0)) (U @ psi' (S (S n))))
           (UUnt_eq_UnUt (S n + (S n + 0)) (psi' (S (S n)))))
        (D @
         Dnt (S n + (S n + 0))
           (U @ Unt (S n + (S n + 0)) (U @ psi' (S (S n)))))
        (eq_sym
           (DDnt_eq_DnDt (S n + (S n + 0))
              (U @ Unt (S n + (S n + 0)) (U @ psi' (S (S n))))))).
Proof.
intro n.
simpl.
repeat (elim_eq_rect ; simpl).
apply is_cons_snoc.
rewrite <- plus_n_Sm.
exact (is_cons_s_DmUnDnt_Dmt (S n) (n + (n + 0)) (D @ U @ U @ U @ Unt (S (n + (n + 0))) (psi' (S (S n))))).
Qed.

Lemma is_cons_s_DnU2npsin_DSnU2SnpsiSn :
  forall n, 0 < n -> is_cons (s_DnU2npsin_DSnU2SnpsiSn n).
Proof.
intros n H.
unfold s_DnU2npsin_DSnU2SnpsiSn; simpl.
unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
destruct n.
inversion H.
apply is_cons_s_DnU2npsin_DSnU2SnpsiSn_helper.
Qed.

Lemma embed_strict_append_DnU2npsin_DSnU2SnpsiSn :
  forall t n (r : t ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n)))),
    embed_strict r (append r (s_DnU2npsin_DSnU2SnpsiSn (S n))).
Proof.
intros.
apply append_is_cons.
apply is_cons_s_DnU2npsin_DSnU2SnpsiSn.
intuition.
Qed.

Lemma wf_s_psi_DSnU2SnpsiSn :
  forall n : nat, wf (s_psi_DSnU2SnpsiSn n).
Proof.
intro n.
apply wf_finite.
apply finite_s_psi_DSnU2SnpsiSn.
Qed.

Lemma wf_s_psi_repeat_D :
  wf s_psi_repeat_D.
Proof.
split.
apply wf_s_psi_DSnU2SnpsiSn.
intros n m H.
induction H; simpl.
apply embed_strict_append_DnU2npsin_DSnU2SnpsiSn.
apply (embed_strict_trans (q := s_psi_DSnU2SnpsiSn m)).
apply IHle.
apply embed_strict_append_DnU2npsin_DSnU2SnpsiSn.
Qed.

(** * Conclusions

   We conclude by taking our results together, showing this TRS does not
   have the unique normal forms property. We then generalise this to
   show that weak orthogonality does not imply unique normal forms. *)

Lemma no_unique_normal_forms_UD :
  ~ unique_normal_forms UD_trs.
Proof.
intro H.
apply neq_repeat_D_repeat_U.
apply H with psi s_psi_repeat_D s_psi_repeat_U.
exact wf_s_psi_repeat_D.
exact wf_s_psi_repeat_U.
exact normal_form_repeat_D.
exact normal_form_repeat_U.
Qed.

Lemma no_unique_normal_forms_wo :
  ~ forall F X trs, weakly_orthogonal (F := F) (X := X) trs -> unique_normal_forms trs.
Proof.
intro H.
apply no_unique_normal_forms_UD.
apply H.
apply weakly_orthogonal_UD.
Qed.
