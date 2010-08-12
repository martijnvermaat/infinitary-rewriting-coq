Require Import Rewriting.
Require Import Equality.
Require Import NoUniqueNormalFormsWO.

Set Implicit Arguments.

(*
  We show some properties in the weakly orthogonal TRS with rules

    PS : P(S(x)) -> x
    SP : S(P(x)) -> x

  and do it in this file to keep the proof of no_unique_normal_forms_wo
  somewhat consise.
*)

(* Trivial substitution *)
Notation id_sub := (empty_substitution F X).

(* DUDU... *)
CoFixpoint repeat_DU : term :=
  D @ U @ repeat_DU.

(* (Ux, UX) is a critical pair *)
Lemma critical_pair_Ux_Ux : critical_pair UD_trs (U @@ varx!) (U @@ varx!).
Proof.
unfold critical_pair.
exists UD.
exists DU.
exists (0 :: nil).
exists (fun x => match (beq_var x varx) with true => U @@ varx! | false => x! end).
exists id_sub.
split.
right; left; reflexivity.
split.
left; reflexivity.
split.
discriminate.
split.
reflexivity.
split.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
constructor.
intro i.
dependent destruction i.
apply term_bis_refl.
inversion i.
inversion i.
split.
constructor.
intro i.
dependent destruction i.
simpl.
unfold vmap.
simpl.
unfold vcast.
generalize (lt_plus_minus_r (Gt.gt_le_S 0 1 (Lt.lt_0_Sn 0))).
intro e.
dependent destruction e.
simpl.
constructor.
inversion i.
apply term_bis_refl.
Qed.

(* DDD... is infinite (using the coinductive term_inf predicate *)
Lemma term_inf_repeat_D :
  term_inf repeat_D.
Proof.
cofix co.
rewrite (peek_eq repeat_D); simpl.
apply Fun_inf with (First (n := 0)).
assumption.
Qed.

(* UUU... is infinite (using the coinductive term_inf predicate *)
Lemma term_inf_repeat_U :
  term_inf repeat_U.
Proof.
cofix co.
rewrite (peek_eq repeat_U); simpl.
apply Fun_inf with (First (n := 0)).
assumption.
Qed.

(* DDD... is infinite (using the alternative infinite predicate *)
Lemma infinite_repeat_D :
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

(* UUU... is infinite (using the alternative infinite predicate *)
Lemma infinite_repeat_U :
  infinite repeat_U.
Proof.
intro d.
assert (S : exists p : position, position_depth p = d /\ subterm repeat_U p = Some repeat_U).
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

(* DDD... is an infinite normal form *)
Lemma infinite_nf_repeat_D :
  term_inf repeat_D /\ normal_form UD_trs repeat_D.
Proof.
exact (conj term_inf_repeat_D normal_form_repeat_D).
Qed.

(* UUU... is an infinite normal form *)
Lemma infinite_nf_repeat_U :
  term_inf repeat_U /\ normal_form UD_trs repeat_U.
Proof.
exact (conj term_inf_repeat_U normal_form_repeat_U).
Qed.

(* DDD... and UUU... are the only infinite normal forms *)
(* Using coinductive infinite predicate *)
Lemma repeat_D_repeat_U_only_infinite_normal_forms :
  forall t,
    term_inf t /\ normal_form UD_trs t ->
    t [~] repeat_D \/ t [~] repeat_U.
Proof.
(* this is a very ugly proof *)
intros [x | [] args] [It Nt].

inversion It.

left.
assert (H : term_eq_up_to 1 (@Fun F X D args) repeat_D).
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
constructor.
apply term_eq_implies_term_bis.
intro n.
generalize dependent (@Fun F X D args).
induction n as [| n IH]; intros t It Nt H.
constructor.
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
clear H.
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.

apply IH; clear IH.
inversion It.
dependent destruction H1.
revert H0.
dependent destruction i.
trivial.
inversion i.

intros [c [r [u [H1 H2]]]].
apply Nt.
exists (D @@@ c).
exists r.
exists u.
split.
assumption.
simpl.
constructor.
intro i.
dependent destruction i.
assumption.
inversion i.

(* contradict this with Nt *)
assert (Hx : ~ exists w, v First = @Fun F X U w).
intro Hx.
unfold normal_form in Nt.
apply Nt.
clear It Nt. (* readability *)
destruct Hx as [w H].
exists Hole.
exists DU.
exists (fun n => w First).
split.
left; reflexivity.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
rewrite H.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
apply term_bis_refl.
inversion i.
inversion i.
clear Nt.

inversion It.
clear It.
dependent destruction H1.
revert H0.
dependent destruction i.
intro It.
destruct (v First).
inversion It.
destruct f.
rewrite (peek_eq repeat_D); simpl.
constructor.
constructor.
contradict Hx.
exists v0.
reflexivity.
inversion i.
inversion i.

(* Same argument follows *)

right.
assert (H : term_eq_up_to 1 (@Fun F X U args) repeat_U).
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
constructor.
apply term_eq_implies_term_bis.
intro n.
generalize dependent (@Fun F X U args).
induction n as [| n IH]; intros t It Nt H.
constructor.
rewrite (peek_eq repeat_U) in H.
dependent destruction H.
clear H.
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.

apply IH; clear IH.
inversion It.
dependent destruction H1.
revert H0.
dependent destruction i.
trivial.
inversion i.

intros [c [r [u [H1 H2]]]].
apply Nt.
exists (U @@@ c).
exists r.
exists u.
split.
assumption.
simpl.
constructor.
intro i.
dependent destruction i.
assumption.
inversion i.

(* contradict this with Nt *)
assert (Hx : ~ exists w, v First = @Fun F X D w).
intro Hx.
unfold normal_form in Nt.
apply Nt.
clear It Nt. (* readability *)
destruct Hx as [w H].
exists Hole.
exists UD.
exists (fun n => w First).
split.
right; left; reflexivity.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
rewrite H.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
apply term_bis_refl.
inversion i.
inversion i.
clear Nt.

inversion It.
clear It.
dependent destruction H1.
revert H0.
dependent destruction i.
intro It.
destruct (v First).
inversion It.
destruct f.
contradict Hx.
exists v0.
reflexivity.
rewrite (peek_eq repeat_U); simpl.
constructor.
constructor.
inversion i.
inversion i.
Qed.

(* DDD... and UUU... are the only infinite normal forms *)
(* Using alternative infinite predicate via positions *)
Lemma repeat_D_repeat_U_only_infinite_normal_forms_alt :
  forall t,
    infinite t /\ normal_form UD_trs t ->
    t [~] repeat_D \/ t [~] repeat_U.
Proof.
(* this is a very ugly proof *)
intros [x | [] args] [It Nt].

destruct (It 1) as [p [Dp Hp]].
contradict Hp.
destruct p as [| a [| b p]].
discriminate Dp.
reflexivity.
discriminate Dp.

left.
assert (H : term_eq_up_to 1 (@Fun F X D args) repeat_D).
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
constructor.
apply term_eq_implies_term_bis.
intro n.
generalize dependent (@Fun F X D args).
induction n as [| n IH]; intros t It Nt H.
constructor.
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
clear H.
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.

apply IH; clear IH.
intro d.
assert (H := It (S d)).
destruct H as [p [H1 H2]].
dependent destruction p.
exists p.
split.
reflexivity.
destruct n0.
assumption.
contradict H2.
reflexivity.

intros [c [r [u [H1 H2]]]].
apply Nt.
exists (D @@@ c).
exists r.
exists u.
split.
assumption.
simpl.
constructor.
intro i.
dependent destruction i.
assumption.
inversion i.

(* contradict this with Nt *)
assert (Hx : ~ exists w, v First = @Fun F X U w).
intro Hx.
unfold normal_form in Nt.
apply Nt.
clear It Nt. (* readability *)
destruct Hx as [w H].
exists Hole.
exists DU.
exists (fun n => w First).
split.
left; reflexivity.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
rewrite H.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
apply term_bis_refl.
inversion i.
inversion i.
clear Nt.

unfold infinite in It.
specialize It with 2.
destruct It as [p [H1 H2]].
destruct p as [| [| a] [| b [| c p]]].
inversion H1.
inversion H1.
simpl in H2.
unfold vhead in H2.
destruct (v First).
contradict H2.
reflexivity.
destruct f.
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
constructor.
contradict Hx.
exists v0.
reflexivity.
inversion H1.
inversion H1.
contradict H2.
reflexivity.
inversion H1.
inversion i.

(* Same argument follows *)

right.
assert (H : term_eq_up_to 1 (@Fun F X U args) repeat_U).
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
constructor.
apply term_eq_implies_term_bis.
intro n.
generalize dependent (@Fun F X U args).
induction n as [| n IH]; intros t It Nt H.
constructor.
rewrite (peek_eq repeat_U) in H.
dependent destruction H.
clear H.
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.

apply IH; clear IH.
intro d.
assert (H := It (S d)).
destruct H as [p [H1 H2]].
dependent destruction p.
exists p.
split.
reflexivity.
destruct n0.
assumption.
contradict H2.
reflexivity.

intros [c [r [u [H1 H2]]]].
apply Nt.
exists (U @@@ c).
exists r.
exists u.
split.
assumption.
simpl.
constructor.
intro i.
dependent destruction i.
assumption.
inversion i.

(* contradict this with Nt *)
assert (Hx : ~ exists w, v First = @Fun F X D w).
intro Hx.
unfold normal_form in Nt.
apply Nt.
clear It Nt. (* readability *)
destruct Hx as [w H].
exists Hole.
exists UD.
exists (fun n => w First).
split.
right; left; reflexivity.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
rewrite H.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
apply term_bis_refl.
inversion i.
inversion i.
clear Nt.

unfold infinite in It.
specialize It with 2.
destruct It as [p [H1 H2]].
destruct p as [| [| a] [| b [| c p]]].
inversion H1.
inversion H1.
simpl in H2.
unfold vhead in H2.
destruct (v First).
contradict H2.
reflexivity.
destruct f.
contradict Hx.
exists v0.
reflexivity.
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
constructor.
inversion H1.
inversion H1.
contradict H2.
reflexivity.
inversion H1.
inversion i.
Qed.

(* We use context_ind2 in the following proof. *)
Section InductionPrinciple.

  Variable P : context -> Type.

  Hypothesis H1 : P Hole.

  Hypothesis H2 :
    forall (f : F) (i j : nat) (e : i + S j = arity f) (v : terms i)
      (w : terms j),
      P (CFun f e v Hole w).

  Hypothesis H3 :
    forall (f : F) (i j : nat) (e : i + S j = arity f) (v : terms i)
      (w : terms j)
      (g : F) (n m : nat) (a : n + S m = arity g) (x : terms n)
      (c : context) (z : terms m),
      P c ->
      P (CFun f e v (CFun g a x c z) w).

  Fixpoint context_rect2 c : P c :=
    match c return P c with
    | Hole                                  => H1
    | CFun f i j e v Hole w                 => H2 f e v w
    | CFun f i j e v (CFun g n m a x c z) w => H3 f e v w g a x z (context_rect2 c)
    end.

End InductionPrinciple.

Definition context_ind2 (P : context -> Prop) :=
  context_rect2 P.

(* DUDU... rewrites only to itself *)
Lemma repeat_DU_rewrites_to_itself :
  forall t (p : repeat_DU [>] t),
    t [~] repeat_DU.
Proof.
intros s p.
dependent destruction p.
destruct i as [H | [H | []]]; try (rewrite <- H in t1, t0; clear H).

unfold DU, lhs, DU_l in t0.
unfold DU, rhs, DU_r in t1.
apply term_bis_trans with (fill c (substitute u (varx!))).
exact (term_bis_symm t1).
clear t1.

assert ((substitute u (D @@ U @@ varx!)) [~] repeat_DU).
induction c using context_ind2; simpl in t0.
assumption.

(* absurd case *)
rewrite (peek_eq repeat_DU) in t0.
simpl in t0.
dependent destruction t0.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
dependent destruction H.

apply IHc; clear IHc.
rewrite (peek_eq repeat_DU) in t0.
simpl in t0.
dependent destruction t0.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
dependent destruction H.
specialize H with (First (n := 0)).
simpl in H.
assert (nm : n = 0 /\ m = 0).
destruct n as [| [| n]]; auto; discriminate a.
revert a x z H.
rewrite (proj1 nm).
rewrite (proj2 nm).
simpl.
intro a.
clear n m nm.
dependent destruction a.
simpl.
intros x z H.
assumption.

assert (substitute u (varx!) [~] repeat_DU).
dependent destruction H.
specialize H with (First (n := 0)).
unfold vmap in H.
simpl in H.
dependent destruction H.
specialize H with (First (n := 0)).
unfold vmap in H.
simpl in H.
rewrite (peek_eq repeat_DU) in x0.
dependent destruction x0.
assumption.

assert (substitute u (D @@ U @@ varx!) [~] substitute u (varx!)).
apply term_bis_trans with repeat_DU.
assumption.
apply term_bis_symm.
assumption.
clear H H0.

(* TODO: This should be a separate lemma *)
generalize dependent (substitute u (varx!)).
generalize dependent (substitute u (D @@ U @@ varx!)).
generalize dependent repeat_DU.
clear t r u.

induction c as [| [] i j e v c IH w]; intros s t H1 u H2; simpl in H1.
apply term_bis_trans with t.
apply term_bis_symm.
assumption.
assumption.

dependent destruction H1.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
constructor.
intro i.
dependent destruction i.
simpl.
apply IH with t.
assumption.
assumption.
inversion i.

dependent destruction H1.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
constructor.
intro i.
dependent destruction i.
simpl.
apply IH with t.
assumption.
assumption.
inversion i.

(* This case is the same as the previous *)

unfold UD, lhs, UD_l in t0.
unfold UD, rhs, UD_r in t1.
apply term_bis_trans with (fill c (substitute u (varx!))).
exact (term_bis_symm t1).
clear t1.

destruct c; simpl in t0 |- *; rewrite (peek_eq repeat_DU) in t0; simpl in t0;
dependent destruction t0.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v v0 H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v v0 H.
clear v.

change (fill c (substitute u (U @@ D @@ varx!)) [~] (U @ repeat_DU)) in H.
assert ((substitute u (U @@ D @@ varx!)) [~] (U @ repeat_DU)).
induction c using context_ind2; simpl in H.
assumption.

(* absurd case *)
dependent destruction H.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
rewrite (peek_eq repeat_DU) in H.
simpl in H.
dependent destruction H.

apply IHc; clear IHc.
rewrite (peek_eq repeat_DU) in H.
simpl in H.
dependent destruction H.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
dependent destruction H.
specialize H with (First (n := 0)).
simpl in H.
assert (nm : n = 0 /\ m = 0).
destruct n as [| [| n]]; auto; discriminate a.
revert a x z H.
rewrite (proj1 nm).
rewrite (proj2 nm).
simpl.
intro a.
clear n m nm.
dependent destruction a.
simpl.
intros x z H.
assumption.

assert (substitute u (varx!) [~] (U @ repeat_DU)).
dependent destruction H0.
specialize H0 with (First (n := 0)).
unfold vmap in H0.
simpl in H.
dependent destruction H0.
specialize H0 with (First (n := 0)).
unfold vmap in H0.
simpl in H0.
rewrite (peek_eq repeat_DU) in x.
dependent destruction x.
assumption.

assert (substitute u (U @@ D @@ varx!) [~] substitute u (varx!)).
apply term_bis_trans with (U @ repeat_DU).
assumption.
apply term_bis_symm.
assumption.
clear H0 H1.

rewrite (peek_eq (repeat_DU)).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.
clear v0.
change (fill c (substitute u (varx!)) [~] (U @ repeat_DU)).

(* TODO: This should be a separate lemma *)
generalize dependent (substitute u (varx!)).
generalize dependent (substitute u (U @@ D @@ varx!)).
generalize dependent (U @ repeat_DU).
clear t r u.

induction c as [| [] i j e v c IH w]; intros s t H1 u H2; simpl in H1.
apply term_bis_trans with t.
apply term_bis_symm.
assumption.
assumption.

dependent destruction H1.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
constructor.
intro i.
dependent destruction i.
simpl.
apply IH with t.
assumption.
assumption.
inversion i.

dependent destruction H1.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
constructor.
intro i.
dependent destruction i.
simpl.
apply IH with t.
assumption.
assumption.
inversion i.
inversion i.
Qed.

(* Now some example rewrite sequences *)

(* Zero-step reduction psi ->> psi *)
Definition s_psi_psi : psi ->> psi := Nil' psi.

(* Substitution for step psi -> U @ psi' 1 *)
Definition sub_psi_Upsi1 (x : X) : term := U @ psi' 1.

Lemma fact_term_bis_psi :
  fill Hole (substitute sub_psi_Upsi1 (lhs DU)) [~] psi.
Proof.
rewrite (peek_eq psi).
simpl.
constructor.
intro i; simpl in i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
(* this is really annoying, but i guess there's no way around it... *)
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => psi' 1
      | S u0 => U @ U @ U2nt u0
      end) 1)).
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => psi' 1
       | S u0 => U @ U @ U2nt u0
       end) 0)).
simpl.
constructor.
unfold vmap.
intro i.
dependent destruction i; [idtac | inversion i].
unfold sub_psi_Upsi1.
simpl.
rewrite (peek_eq (psi' 1)).
apply term_bis_refl.
Qed.

(* Step psi -> U @ psi' 1 *)
Definition p_psi_Upsi1 : psi [>] (U @ psi' 1) :=
  Step DU Hole sub_psi_Upsi1 DU_in fact_term_bis_psi (term_bis_refl (U @ psi' 1)).

(* Single-step reduction psi ->> U @ psi' 1 *)
Definition s_psi_Upsi1 : psi ->> (U @ psi' 1) :=
  Cons s_psi_psi p_psi_Upsi1.

(* Substitution for step U @ psi' 1 -> U D D U U U @ psi' 2 *)
Definition sub_Upsi1_UDDUUUpsi2 (x : X) : term := U @ U @ U @ psi' 2.

Lemma fact_term_bis_Upsi1 :
  fill (U @@@ D @@@ D @@@ Hole) (substitute sub_Upsi1_UDDUUUpsi2 (lhs DU))
  [~]
  (U @ psi' 1).
Proof.
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
rewrite (peek_eq (psi' 1)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
       match d with
       | 0 =>
           D @
           (cofix U2nt (u : nat) : term :=
              match u with
              | 0 => psi' 2
              | S u0 => U @ U @ U2nt u0
              end) 2
       | S d0 => D @ D @ D2nDt d0
       end) 0)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => psi' 2
      | S u0 => U @ U @ U2nt u0
      end) 2)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
unfold sub_Upsi1_UDDUUUpsi2.
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => psi' 2
      | S u0 => U @ U @ U2nt u0
      end) 1)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
generalize (psi' 2).
intro t.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) 0)).
simpl.
destruct t; apply term_bis_U; apply term_bis_refl.
Qed.

(* Step U @ psi' 1 -> U D D U U U @ psi' 2 *)
Definition p_Upsi1_UDDUUUpsi2 : (U @ psi' 1) [>] (U @ D @ D @ U @ U @ U @ psi' 2) :=
  Step DU (U @@@ D @@@ D @@@ Hole) sub_Upsi1_UDDUUUpsi2 DU_in fact_term_bis_Upsi1 (term_bis_refl (U @ D @ D @ U @ U @ U @ psi' 2)).

(* Two-step reduction psi ->> U D D U U U @ psi' 2 *)
Definition s_psi_UDDUUUpsi2 : psi ->> (U @ D @ D @ U @ U @ U @ psi' 2) := Cons s_psi_Upsi1 p_Upsi1_UDDUUUpsi2.

(* Helper lemma for the following *)
Lemma all_terms_eq_up_to_d_s_UdDnUnt_Udt_repeat_U :
  forall d n t,
    all_terms_eq_up_to d (s_UmDnUnt_Umt d n t) repeat_U.
Proof.
intros d n t.
induction n as [| n IH]; simpl.
apply term_eq_up_to_n_Unt_repeat_U.
apply all_terms_eq_up_to_snoc.
apply term_eq_up_to_n_Unt_repeat_U.
apply IH.
Qed.

(* This would amount to most of weak convergence condition, except that it
   is not this easy to state. *)
Lemma all_terms_eq_up_to_d_s_Udpsid_USdpsiSd_repeat_U :
  forall d,
    all_terms_eq_up_to d (s_Unpsin_USnpsiSn d) repeat_U.
Proof.
intro d.
unfold s_Unpsin_USnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
apply all_terms_eq_up_to_snoc.
apply term_eq_up_to_n_Unt_repeat_U.
apply all_terms_eq_up_to_d_s_UdDnUnt_Udt_repeat_U.
Qed.

(*
   What follows is an alternative (actually the original) definition of psi
   and (almost) a proof that it is equal to the new psi used above.
*)

(* D^n U^Sn D^SSn U^SSSn ... *)
CoFixpoint oldpsi' n : term :=
  (cofix Dnt (d : nat) :=
    match d with
    | O   => (cofix USnt (u : nat) :=
               match u with
               | O   => U @ oldpsi' (S (S n))
               | S u => U @ (USnt u)
               end) (S n)
    | S d => D @ (Dnt d)
    end) (S n).

(* DUUDDDUUUU... *)
Definition oldpsi := oldpsi' 0.

Lemma UUSnt_eq_USnUt :
  forall n t,
    (U @ (cofix USnt (u : nat) : term :=
            match u with
            | 0 => t
            | S u0 => U @ USnt u0
            end) n)
    =
    (cofix USnt (u : nat) : term :=
       match u with
       | 0 => U @ t
       | S u0 => U @ USnt u0
       end) n.
Proof.
induction n; intro t.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ USnt u0
      end) 0)).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ USnt u0
       end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ USnt u0
       end) (S n))).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ USnt u0
      end) (S n))).
simpl.
rewrite IHn with t.
reflexivity.
Qed.

(* Terrible lemma that should help proving psi n and oldpsi 2n equal *)
Lemma helper :
  forall n t,
    (cofix D2nDt (d : nat) :=
      match d with
      | O   => D @ (cofix U2nt (u : nat) :=
                 match u with
                 | O   => t
                 | S u => U @ U @ (U2nt u)
                 end) (S n)
      | S d => D @ D @ (D2nDt d)
      end) n
    =
    (cofix Dnt (d : nat) :=
      match d with
      | O   => (cofix USnt (u : nat) :=
                 match u with
                 | O   => U @ t
                 | S u => U @ (USnt u)
                 end) (S (n + n))
      | S d => D @ (Dnt d)
      end) (S (2 * n)).
Proof.
induction n; intro t; simpl.
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
      match d with
      | 0 =>
          D @
          (cofix U2nt (u : nat) : term :=
             match u with
             | 0 => t
             | S u0 => U @ U @ U2nt u0
             end) 1
      | S d0 => D @ D @ D2nDt d0
      end) 0)).
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
                match u with
                | 0 => t
                | S u0 => U @ U @ U2nt u0
                end) 1)).
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ t
             | S u0 => U @ USnt u0
             end) 1
      | S d0 => D @ Dnt d0
      end) 1)).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ t
             | S u0 => U @ USnt u0
             end) 1)).
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) 0)).
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          U @
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ t
             | S u0 => U @ USnt u0
             end) 0
      | S d0 => D @ Dnt d0
      end) 0)).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
                match u with
                | 0 => U @ t
                | S u0 => U @ USnt u0
                end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
      match d with
      | 0 =>
          D @
          (cofix U2nt (u : nat) : term :=
             match u with
             | 0 => t
             | S u0 => U @ U @ U2nt u0
             end) (S (S n))
      | S d0 => D @ D @ D2nDt d0
      end) (S n))).
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
             match u with
             | 0 => t
             | S u0 => U @ U @ U2nt u0
             end) (S (S n)))).
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ t
             | S u0 => U @ USnt u0
             end) (S (S (n + S n)))
      | S d0 => D @ Dnt d0
      end) (S (S (n + S (n + 0)))))).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
                match u with
                | 0 => U @ t
                | S u0 => U @ USnt u0
                end) (S (S (n + S n))))).
simpl.
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
       match d with
       | 0 =>
           U @
           (cofix USnt (u : nat) : term :=
              match u with
              | 0 => U @ t
              | S u0 => U @ USnt u0
              end) (S (n + S n))
       | S d0 => D @ Dnt d0
       end) (S (n + S (n + 0))))).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
                 match u with
                 | 0 => U @ t
                 | S u0 => U @ USnt u0
                 end) (S (n + S n)))).
simpl.
rewrite UU2nt_eq_U2nUt_unfolded with (S n) t.
rewrite UU2nt_eq_U2nUt_unfolded with (S n) (U @ t).
rewrite IHn with (U @ U @ t).
rewrite UUSnt_eq_USnUt with (n + S n) (U @ t).
rewrite UUSnt_eq_USnUt with (n + S n) (U @ U @ t).
simpl.
rewrite (eq_sym (plus_n_Sm n n)).
rewrite (eq_sym (plus_n_Sm n (n + 0))).
reflexivity.
Qed.

Lemma bb :
  forall n t,
    (U @
    (cofix USnt (u : nat) : term :=
      match u with
        | 0 => t
        | S u0 => U @ USnt u0
      end) n)
    =
    (cofix USnt (u : nat) : term :=
      match u with
        | 0 => U @ t
        | S u0 => U @ USnt u0
      end) n.
Proof.
induction n; intro t; simpl.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ USnt u0
       end) 0)).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ USnt u0
      end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ USnt u0
       end) (S n))).
simpl.
rewrite (IHn t).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ USnt u0
      end) (S n))).
simpl.
reflexivity.
Qed.

Lemma aa :
  forall n t,
  (cofix Dnt (d : nat) : term :=
    match d with
      | 0 =>
        (cofix USnt (u : nat) : term :=
          match u with
            | 0 => t
            | S u0 => U @ USnt u0
          end) (S (n + n))
      | S d0 => D @ Dnt d0
    end) (n + n)
  =
  Dnt (2 * n) (Unt (S (2 * n)) t).
Proof.
induction n; intro t; simpl.
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => t
             | S u0 => U @ USnt u0
             end) 1
      | S d0 => D @ Dnt d0
      end) 0)).
simpl.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ USnt u0
       end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => t
             | S u0 => U @ USnt u0
             end) (S (S (n + S n)))
      | S d0 => D @ Dnt d0
      end) (S (n + S n)))).
simpl.
rewrite <- (plus_n_Sm n (n + 0)).
simpl.
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
       match d with
       | 0 =>
           (cofix USnt (u : nat) : term :=
              match u with
              | 0 => t
              | S u0 => U @ USnt u0
              end) (S (S (n + S n)))
       | S d0 => D @ Dnt d0
       end) (n + S n))).
simpl.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
              match u with
              | 0 => t
              | S u0 => U @ USnt u0
              end) (S (S (n + S n))))).
simpl.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
              match u with
              | 0 => t
              | S u0 => U @ USnt u0
              end) (S (n + S n)))).
simpl.
rewrite (bb (n + S n) t).
rewrite (bb (n + S n) (U @ t)).
rewrite <- plus_n_Sm.
rewrite (IHn (U @ U @ t)).
simpl.
rewrite <- UUnt_eq_UnUt.
rewrite <- UUnt_eq_UnUt.
reflexivity.
Qed.

Lemma ccD :
  forall n s t,
    s [~] t ->
    Dnt n s [~] Dnt n t.
Proof.
intros.
induction n; simpl.
assumption.
constructor.
intro i.
dependent destruction i.
simpl.
assumption.
inversion i.
Qed.

Lemma ccU :
  forall n s t,
    s [~] t ->
    Unt n s [~] Unt n t.
Proof.
intros.
induction n; simpl.
assumption.
constructor.
intro i.
dependent destruction i.
simpl.
assumption.
inversion i.
Qed.

Lemma psin_eq_oldpsi2n :
  forall n,
    psi' n [~] oldpsi' (2 * n).
Proof.
(* TODO: should be somehow possible to show, using lemma helper, but the
   strategy below is faulty (not guarded) *)
cofix c.
intro n.
rewrite (peek_eq (psi' n)).
simpl.
assert (H := helper n (psi' (S n))).
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
         match d with
         | 0 =>
             D @
             (cofix U2nt (u : nat) : term :=
                match u with
                | 0 => psi' (S n)
                | S u0 => U @ U @ U2nt u0
                end) (S n)
         | S d0 => D @ D @ D2nDt d0
         end) n)) in H.
simpl in H.
rewrite H.
clear H.
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ psi' (S n)
             | S u0 => U @ USnt u0
             end) (S (n + n))
      | S d0 => D @ Dnt d0
      end) (S (n + (n + 0))))).
rewrite (peek_eq (oldpsi' (n + (n + 0)))).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite <- plus_n_O.
rewrite (aa n (U @ psi' (S n))).
rewrite (aa n (U @ oldpsi' (S (S (n + n))))).
rewrite <- UUnt_eq_UnUt.
rewrite <- UUnt_eq_UnUt.
apply ccD.
apply (ccU (S (S (2 * n)))).
rewrite plus_n_Sm.
pattern (S n) at 2.
rewrite plus_n_O.
rewrite plus_Sn_m.
specialize c with (S n).
simpl in c.
exact c.
(* so the proof is not guarded now *)
Admitted.

(* This increases confidence in correctness of psi :) *)
Lemma psi_eq_oldpsi :
  psi [~] oldpsi.
Proof.
apply psin_eq_oldpsi2n.
Qed.
