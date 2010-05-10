Require Import Rewriting.

Set Implicit Arguments.

(*
  We construct the weakly orthogonal TRS with rules

    PS : P(S(x)) -> x
    SP : S(P(x)) -> x

  and show it is a counterexample to UN-inf.
*)

(* Signature *)

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

(* Variables *)

Definition variable : Set := nat.

Fixpoint beq_var (x y : variable) : bool :=
  match x, y with
  | 0, 0       => true
  | S x', S y' => beq_var x' y'
  | _,    _    => false
end.

Lemma beq_var_ok : forall x y, beq_var x y = true <-> x = y.
Proof.
induction x as [|x IH]; destruct y;
  simpl; split; intro H; try (reflexivity || discriminate).
  f_equal. exact (proj1 (IH _) H).
  apply (proj2 (IH _)). inversion H. reflexivity.
Qed.

(* Terms *)

Definition F : signature := Signature arity beq_symb_ok.
Definition X : variables := Variables beq_var_ok.

Notation term := (term F X).
Notation fterm := (finite_term F X).

(* Variables *)
Notation "x !" := (@FVar F X x) (at level 75).

(* Function application with one argument *)
Notation "f @ a" := (@Fun F X f (vcons a (vnil term))) (right associativity, at level 75).
Notation "f @@ a" := (@FFun F X f (vcons a (vnil fterm))) (right associativity, at level 75).

(* U(U(U(...))) *)
CoFixpoint repeat_U : term :=
  U @ repeat_U.

(* D(D(D(...))) *)
CoFixpoint repeat_D : term :=
  D @ repeat_D.

(* D(U(D(U(...)))) *)
(* TODO: better to define repeat_DU and repeat_UD together? *)
CoFixpoint repeat_DU : term :=
  D @ U @ repeat_DU.

(* U(U(U(...t...))) *)
Fixpoint SnU (n : nat) t :=
  match n with
  | O   => t
  | S n => U @ (SnU n t)
  end.

(* D(D(D(...t...))) *)
Fixpoint SnD (n : nat) t :=
  match n with
  | O   => t
  | S n => D @ (SnD n t)
  end.

(*
   We would like to define psi' like this

     CoFixpoint psi' n : term :=
       SnU n (SnD (S n) (psi' (S (S n)))).

   but unfortunately this is not guarded.
*)

(* D(U(U(D(D(D(U(U(U(U(...)))))))))) *)
CoFixpoint psi' n : term :=
  (cofix SnD (d : nat) :=
    match d with
    | O   => (cofix SnU (u : nat) :=
                 match u with
                 | O   => U @ psi' (S (S n))
                 | S u => U @ (SnU u)
                 end) (S n)
    | S d => D @ (SnD d)
    end) (S n).

Definition psi := psi' 0.

(* Contexts *)

Notation context := (context F X).

(* Function application with one argument *)
Notation "f @@@ a" := (@CFun F X f 0 0 (@refl_equal nat (arity f)) (vnil term) a (vnil term)) (right associativity, at level 75).

Notation id_sub := (empty_substitution F X).

(* Rewriting *)

Notation trs := (trs F X).

(* D(U(x)) -> x *)
Definition DU_l : fterm := D @@ U @@ 1!.
Definition DU_r : fterm := 1!.

Lemma DU_wf :
  is_var DU_l = false /\
  incl (vars DU_r) (vars DU_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition DU : rule := Rule DU_l DU_r DU_wf.

(* U(D(x)) -> x *)
Definition UD_l : fterm := U @@ D @@ 1!.
Definition UD_r : fterm := 1!.

Lemma UD_wf :
  is_var UD_l = false /\
  incl (vars UD_r) (vars UD_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition UD : rule := Rule UD_l UD_r UD_wf.

Definition UNWO_trs : trs := DU :: UD :: nil.

Lemma UNWO_left_linear :
  trs_left_linear UNWO_trs.
Proof.
split; [| split];
  unfold left_linear; unfold linear; simpl;
    constructor.
intro; assumption.
constructor.
intro; assumption.
constructor.
Qed.

(* D(D(D(...))) is infinite *)
Lemma infinite_D :
  infinite repeat_D.
Proof.
intro d.
assert (S : exists p : position, position_depth p = d /\ subterm repeat_D p = Some repeat_D).
exists ((fix z n := match n with O => nil | S n => 0 :: (z n) end) d).
induction d; split.
reflexivity.
reflexivity.
simpl.
f_equal.
apply IHd.
simpl.
apply IHd.
destruct S as [p S].
exists p.
split.
apply S.
rewrite (proj2 S).
discriminate.
Qed.

Require Import Equality.

(* D(D(D(...))) is a normal form *)
Lemma nf_D :
  normal_form (system := UNWO_trs) repeat_D.
Proof.
(* TODO: a lot of this proof is a mess, cleanup
   Also, I expect that this could be generalized and shortened quite a bit
   by using pos_eq. *)
intros [c [r [u [H1 H2]]]].
destruct H1 as [H1 | H1].
rewrite <- H1 in *|-.
clear H1.
assert (H := H2 (S (S (hole_depth c)))).
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
assert (H' := H First).
rewrite (peek_eq repeat_D) in H'.
dependent destruction H'.
assert (H' := H0 First).
simpl in H'.

(* idea, make [=]1 from x0 *)
assert (y0 : term_eq_up_to 1 (@Fun F X D v) (fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm)))))).
(*assert (y0 : @Fun F X D v [=] fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm))))).*)
rewrite x0.
apply term_eq_up_to_refl.
clear x0.

induction c.

assert (H3 := H2 2).
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
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X D (vcons (fill c (substitute u (lhs DU))) v2)) (D @ repeat_D)).
assert (jaja : fill (@CFun F X D 0 0 e v1 c v2) (substitute u (lhs DU)) = @Fun F X D (vcons (fill c (substitute u (lhs DU))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact (H2 (S n)).
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
assert (H2' := term_eq_implies_term_bis H2).
dependent destruction H2'.
assert (H3 := H First).
simpl in H3.
clear H2 H.
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

admit. (* same argument as above for r=UD instead of r=DU *)
Admitted.

(* U(U(U(...))) is a normal form *)
Lemma nf_U :
  normal_form (system := UNWO_trs) repeat_U.
Proof.
Admitted.

(* D(D(D(...))) is an infinite normal form *)
Lemma infinite_nf_D :
  infinite repeat_D /\ normal_form (system := UNWO_trs) repeat_D.
Proof.
exact (conj infinite_D nf_D).
Qed.

(* U(U(U(...))) is an infinite normal form *)
Lemma infinite_nf_U :
  infinite repeat_U /\ normal_form (system := UNWO_trs) repeat_U.
Proof.
Admitted.

(* D(D(D(...))) and U(U(U(...))) are different *)
Lemma neq_D_U :
  ~ repeat_D [~] repeat_U.
Proof.
intro H.
rewrite (peek_eq repeat_D), (peek_eq repeat_U) in H.
inversion H.
Qed.

(* D(D(D(...))) and U(U(U(...))) are the only infinite normal forms *)
Lemma only_infinite_nf_D_U :
  forall t,
    infinite t /\ normal_form (system := UNWO_trs) t ->
    t [=] repeat_D \/ t [=] repeat_U.
Proof.
(* We should be able to prove this, but it's probably a lot of work *)
intros [x | [] args] [It Nt].

destruct (It 1) as [p [Dp Hp]].
contradict Hp.
destruct p as [| a [| b p]].
discriminate Dp.
reflexivity.
discriminate Dp.

left.
admit.

right.
admit.
Admitted.

(* Reductions *)
Notation Step := (Step UNWO_trs).
Notation Nil := (Nil UNWO_trs).

Notation "s [>] t" := (step UNWO_trs s t) (at level 40).
Notation "s ->> t" := (sequence UNWO_trs s t) (at level 40).

Lemma DU_in :
  In DU UNWO_trs.
Proof.
left; reflexivity.
Qed.

Lemma UD_in :
  In UD UNWO_trs.
Proof.
right; left; reflexivity.
Qed.

Generalizable All Variables.

(* D(U(D(U(...)))) rewrites only to itself *)
Lemma rewrites_to_itself_DU :
  forall `(p : repeat_DU [>] t),
    t [=] repeat_DU.
Proof.
intros s p.
dependent destruction p.
destruct i as [H | [H | H]]; try (rewrite <- H in t1, t0; clear H).

unfold DU, lhs, DU_l in t0.
unfold DU, rhs, DU_r in t1.
apply term_eq_trans with (fill c (substitute u (1 !))).
exact (term_eq_symm t1).
clear t1.
induction c as [| f i j e v c IH w]; simpl in t0 |- *.

(* This does not seem to be the right way, we cannot prove the induction step *)

(* from t0 deduce u 1 [=] repeat_DU, then transitivity of [=] *)
intro n.
assert (H := t0 (S (S n))).
rewrite (peek_eq repeat_DU) in H.
dependent destruction H.
assert (H1 := H First).
dependent destruction H1.
assert (H2 := H0 First).
rewrite (peek_eq repeat_DU) in H2.
dependent destruction H2.
constructor.
unfold vmap in x; simpl in x.
rewrite <- x.
rewrite (peek_eq repeat_DU).
simpl.
constructor.
assumption.

(*apply IH; clear IH.*)
admit. (* more work *)

admit. (* same as previous case *)

contradict H.
Qed.

(* Zero-step reduction psi ->> psi *)
Definition s_psi0 : psi' 0 ->> psi' 0 := Nil (psi' 0).

(* Substitution for step psi' 0 -> U @ psi' 2 *)
Definition sub_psi0_Upsi2 (x : X) : term :=
  match x with
  | 1 => U @ psi' 2
  | _ => Var x
  end.

Lemma fact_term_eq_psi0 :
  fill Hole (substitute sub_psi0_Upsi2 (lhs DU)) [=] psi' 0.
Proof.
intro n.
destruct n.
(* TODO: this is a mess and i guess destructing n should
   not be necessary, we would just need to rewrite some
   lemma about vmap in the left term *)
constructor.
rewrite (peek_eq (psi' 0)).
simpl.
constructor.
intro i; simpl in i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
(* this is really annoying, but i guess there's no way around it... *)
rewrite (peek_eq ((cofix SnD (d : nat) : term :=
         match d with
         | 0 =>
             (cofix SnU (u : nat) : term :=
               match u with
                 | 0 => U @ psi' 2
                   | S u0 => U @ SnU u0
                     end) 1
         | S d0 => D @ SnD d0
         end) 0)).
simpl.
rewrite (peek_eq ((cofix SnU (u : nat) : term :=
         match u with
         | 0 => U @ psi' 2
            | S u0 => U @ SnU u0
               end) 0)).
simpl.
destruct n.
constructor.
constructor.
unfold vmap.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
apply term_eq_up_to_refl.
Qed.

(* Step psi' 0 -> U @ psi' 2 *)
Definition p_psi0_Upsi2 : psi' 0 [>] (U @ psi' 2) := Step DU Hole sub_psi0_Upsi2 DU_in fact_term_eq_psi0 (term_eq_refl (U @ psi' 2)).

(* Single-step reduction psi' 0 ->> U @ psi' 2 *)
Definition s_psi0_Upsi2 : psi' 0 ->> (U @ psi' 2) := Cons s_psi0 p_psi0_Upsi2.

(* Substitution for step U @ psi' 2 -> U D D U U U @ psi' 4 *)
Definition sub_Upsi2_UDDUUUpsi4 (x : X) : term :=
  match x with
  | 1 => U @ U @ U @ psi' 4
  | _ => Var x
  end.

Lemma fact_term_eq_Upsi2 :
  fill (U @@@ D @@@ D @@@ Hole) (substitute sub_Upsi2_UDDUUUpsi4 (lhs DU))
  [=]
  (U @ psi' 2).
Proof.
simpl.
intro n.
destruct n; constructor.
intro i.
dependent destruction i; [idtac | inversion i].
rewrite (peek_eq (psi' 2)).
simpl.
destruct n; constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix SnD (d : nat) : term :=
         match d with
         | 0 =>
             (cofix SnU (u : nat) : term :=
                match u with
                | 0 => U @ psi' 4
                | S u0 => U @ SnU u0
                end) 3
         | S d0 => D @ SnD d0
         end) 2)).
simpl.
destruct n; constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix SnD (d : nat) : term :=
         match d with
         | 0 =>
             (cofix SnU (u : nat) : term :=
                match u with
                | 0 => U @ psi' 4
                | S u0 => U @ SnU u0
                end) 3
         | S d0 => D @ SnD d0
         end) 1)).
simpl.
destruct n; constructor.
intro i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
rewrite (peek_eq ((cofix SnD (d : nat) : term :=
         match d with
         | 0 =>
             (cofix SnU (u : nat) : term :=
                match u with
                | 0 => U @ psi' 4
                | S u0 => U @ SnU u0
                end) 3
         | S d0 => D @ SnD d0
         end) 0)).
simpl.
destruct n; constructor.
intro i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
rewrite (peek_eq ((cofix SnU (u : nat) : term :=
         match u with
         | 0 => U @ psi' 4
         | S u0 => U @ SnU u0
         end) 2)).
simpl.
destruct n; constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix SnU (u : nat) : term :=
         match u with
         | 0 => U @ psi' 4
         | S u0 => U @ SnU u0
         end) 1)).
simpl.
destruct n; constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix SnU (u : nat) : term :=
         match u with
         | 0 => U @ psi' 4
         | S u0 => U @ SnU u0
         end) 0)).
simpl.
apply term_eq_up_to_refl.
Qed.

(* Step U @ psi' 2 -> U D D U U U @ psi' 4 *)
Definition p_Upsi2_UDDUUUpsi4 : (U @ psi' 2) [>] (U @ D @ D @ U @ U @ U @ psi' 4) :=
  Step DU (U @@@ D @@@ D @@@ Hole) sub_Upsi2_UDDUUUpsi4 DU_in fact_term_eq_Upsi2 (term_eq_refl (U @ D @ D @ U @ U @ U @ psi' 4)).

(* Two-step reduction psi' 0 ->> U D D U U U @ psi' 4 *)
Definition s_psi0_UDDUUUpsi4 : psi' 0 ->> (U @ D @ D @ U @ U @ U @ psi' 4) := Cons s_psi0_Upsi2 p_Upsi2_UDDUUUpsi4.

(* Substitution for step U D D U U U @ psi' 4 -> U D U U @ psi' 4 *)
Definition sub_UDDUUUpsi4_UDUUpsi4 (x : X) : term :=
  match x with
  | 1 => U @ U @ psi' 4
  | _ => Var x
  end.

Lemma fact_term_eq_UDDUUUpsi4 :
  fill (U @@@ D @@@ Hole) (substitute sub_UDDUUUpsi4_UDUUpsi4 (lhs DU))
  [=]
  (U @ D @ D @ U @ U @ U @ psi' 4).
Proof.
(* more of the same *)
Admitted.

(* Step U D D U U U @ psi' 4 -> U D U U @ psi' 4*)
Definition p_UDDUUUpsi4_UDUUpsi4 : (U @ D @ D @ U @ U @ U @ psi' 4) [>] (U @ D @ U @ U @ psi' 4) :=
  Step DU (U @@@ D @@@ Hole) sub_UDDUUUpsi4_UDUUpsi4 DU_in fact_term_eq_UDDUUUpsi4 (term_eq_refl (U @ D @ U @ U @ psi' 4)).

(* Three-step reduction psi' 0 ->> U D U U @ psi' 4 *)
Definition s_psi0_UDUUpsi4 : psi' 0 ->> (U @ D @ U @ U @ psi' 4) := Cons s_psi0_UDDUUUpsi4 p_UDDUUUpsi4_UDUUpsi4.

(* Substitution for step U D U U @ psi' 4 -> U U @ psi' 4 *)
Definition sub_UDUUpsi4_UUpsi4 (x : X) : term :=
  match x with
  | 1 => U @ psi' 4
  | _ => Var x
  end.

Lemma fact_term_eq_UDUUpsi4 :
  fill (U @@@ Hole) (substitute sub_UDUUpsi4_UUpsi4 (lhs DU))
  [=]
  (U @ D @ U @ U @ psi' 4).
Proof.
(* more of the same *)
Admitted.

(* Step U D U U @ psi' 4 -> U U @ psi' 4*)
Definition p_UDUUpsi4_UUpsi4 : (U @ D @ U @ U @ psi' 4) [>] (U @ U @ psi' 4) :=
  Step DU (U @@@ Hole) sub_UDUUpsi4_UUpsi4 DU_in fact_term_eq_UDUUpsi4 (term_eq_refl (U @ U @ psi' 4)).

(* Four-step reduction psi' 0 ->> U U @ psi' 4 *)
Definition s_psi0_UUpsi4 : psi' 0 ->> (U @ U @ psi' 4) := Cons s_psi0_UDUUpsi4 p_UDUUpsi4_UUpsi4.

(* psi rewrites to repeat_U *)
Definition s_psi_U : psi ->> repeat_U.
Admitted.

(* psi rewrites to repeat_D *)
Definition s_psi_D : psi ->> repeat_D.
Admitted.

Definition unique_normal_forms :=
  forall t u v,
    t ->> u ->
    t ->> v ->
    normal_form (system := UNWO_trs) u ->
    normal_form (system := UNWO_trs) v ->
    u [~] v.

Lemma no_unique_normal_forms :
  ~ unique_normal_forms.
Proof.
intros H.
apply neq_D_U.
apply (H psi).
exact s_psi_D.
exact s_psi_U.
exact nf_D.
exact nf_U.
Qed.

(* I think we don't need the norm function *)

Require Import ZArith.
Delimit Scope Int_scope with I.

Fixpoint sum (n : nat) (t : term) : Z :=
  match n with
  | 0   => Z0
  | S n => match t with
           | Var _      => Z0
           | Fun D args => vfold (-1)%Z Zplus (vmap (sum n) args)
           | Fun U args => vfold (1)%Z  Zplus (vmap (sum n) args)
           end
  end.

(*
Fixpoint fsum (t : fterm) : Z :=
  match t with
  | FVar _      => Z0
  | FFun D args => vfold (-1)%Z Zplus (vmap fsum args)
  | FFun U args => vfold (1)%Z  Zplus (vmap fsum args)
  end.
*)

(* I have no idea how to implement the norm functions *)
