(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(*  Pierre Casteran 
    LaBRI, Université Bordeaux 1, and Inria Futurs (Logical)
*)

Require Import More_nat.
Require Import Arith.
Require Import ArithRing.
Require Import EPSILON0.



(* Goodstein decompositions are just ordinals *)


(* Conditions on NF to be an item of some Goodstein sequence *)
(* all coefficients must be < n -1                              *)


Inductive correct (N:nat) : T1 -> Prop :=
   Zero_correct : correct N zero
 | Cons_correct : forall (c c' : T1 )(p:nat), (S p < N)%nat ->
                                        correct N c ->
                                        correct N c' ->
                                        correct N (cons c p c').

Lemma correct_succ : forall  N c, correct N c -> 
                                 correct (S N) c.
Proof.
 intros N c;elim c.
 constructor.
 inversion 3.
 constructor; auto.
Qed.



(* value of c if we replace omega with N *)
Fixpoint val (N:nat)(c:T1) {struct c}: nat :=
  match c with 
  | zero => 0
  | cons alpha n beta => ((power N (val N alpha) * (S n)) +
                          val N beta)%nat
  end.

(*
Eval compute in (val 3 (omega^omega + omega*(F 2) + F 2)).
*)

(* the predecessor in base N is central to the proof of Goodstein sequence *)
(* we use a strong specification                                           *)

Section predecessor.
 Variable N0:nat.
 Let N := S (S N0).
 
 Definition pred_spec (c:T1) := {c':T1 | 
                                     nf c'                             /\
                                     (c = zero /\ c'= zero \/ c' < c) /\
                                     val N c' =  
                                     Peano.pred (val N c) 
                                                                        /\
                                     correct N c'}.

 Variable c : T1.
 Hypothesis nf_c : nf c.
 Hypothesis coeff_ok : correct N c.
  
 
 Variable recurr : forall c', correct N c' -> 
                               nf c' -> c' < c -> pred_spec c'.

 (* c = zero :

    take c' = zero *)


 Definition pred_n_zero : pred_spec zero.
  unfold pred_spec.
  exists zero; repeat split.
  constructor.
  left;auto.
  constructor.
 Defined.

 (* c = cons zero (S n) zero
    take c' = zero or cons zero n zero 
 *)

 Definition PredF : forall n , (n < N)%nat -> pred_spec (F (S n)).
  intro n; case n.
  exists zero.
  repeat split.
  constructor.
  simpl;right;constructor.
  left.
  intros p Hp; exists (cons zero  p zero).
  repeat split.
  constructor.
  constructor.
  auto with arith.
  simpl; right; constructor 3.
  auto with arith.
  constructor; [ auto | .. ]; constructor.
 Defined.


 Lemma val_positive:  forall a, zero < a -> nf a -> 
                             forall N, 
                               (0 < val (S (S N)) a)%nat.
 Proof.
  induction a.
  inversion 1.
  simpl.
  intros.
  replace 0 with (0 + 0)%nat.
  apply plus_lt_le_compat.
  2:auto with arith.
  2: simpl;auto.
  replace 0 with (0 * 0)%nat. 
  apply Lt.le_lt_trans with (0 * n)%nat.
  simpl;auto.
  simpl.
  generalize (val (S (S N1)) a1).
  induction n0.
  simpl.
  auto with arith.
  simpl.
  replace 0 with (0 * (S n))%nat.
  apply mult_lt_compat_r.
  replace 0 with (0 + 0)%nat.
  apply plus_lt_le_compat.
  apply power_positive.
  auto with arith.
  simpl;auto.
 auto with arith.
 simpl;auto.
 simpl;auto.
Qed.

(*  if c = omega^a,
    take c' = omega^a' * (N-1) + pred_N (omega^a')
    where a' = pred_N a
*)

Definition Pred_omega_a : forall a, zero < a -> c = cons a 0 zero -> pred_spec c.
 intros.
 subst c.
 assert (nf a).
 eapply nf_inv1; eauto.
 assert (lt a (cons a 0 zero)).
 apply head_lt_cons. 
 (* this part should be lemmified *)

 assert (H23:correct N a).
 inversion coeff_ok;auto.
 pose (a' := recurr a H23 H0 H1).
 case a'.
 intros preda (H2,(H3,(H4,H5))).
 assert (lt preda a).
 case H3.
 intro; absurd (lt zero zero).
 apply lt_irr.
 case H6;intros H61 H62.
 rewrite H61 in H;auto.
 auto.
 assert (lt (cons preda 0 zero) (cons a 0 zero)).
 constructor 2;auto.
 assert (nf (cons preda 0 zero)).
 constructor.
 auto.
 auto with arith.

 assert (H27: correct N (cons preda 0 zero)).
 constructor.
 unfold N; auto with arith.
 auto.
 constructor.
 pose (a'' := recurr (cons preda 0 zero)  H27 H8 H7).
 case a''.
 intros predpred Hs.

 (* building the result *)

 exists (cons preda N0 predpred).
 case Hs;intros.
 clear Hs; case H10;intros.
 clear H10; case H12; intros; clear H12.
 case H11; intro.
 case H12; intros H121 H122. 
 discriminate H121.
 split.
 generalize H9 H12;case predpred.
 constructor.
 auto.
 auto with arith.
 constructor 3.
 inversion_clear H15.
 auto.
 inversion H16.
 inversion H16.
 auto.
 auto.
 split.
 right.
 constructor 2.
 auto.
 split.
 simpl.
 rewrite H10.
 simpl.
 rewrite H4.
 assert (0 < val N a)%nat.
 unfold N.
 eapply  val_positive.
 auto.
 auto.
 Focus 2.
 constructor.
 unfold N; auto.
 auto.
 auto.
 pred_exhib H14 q.
 rewrite e.
 simpl.
 assert (0 < N ^ q)%nat.
 elim q.
 simpl.
 auto with arith.
 simpl.
 intros.
 replace 0 with (0 + 0)%nat.
 apply plus_lt_le_compat.
 auto.
 auto with arith.
 simpl; auto.
 simpl.
 pred_exhib H15 u.
 rewrite e0.
 simpl.
 ring.
Defined.

(*  if c = omega^a*(k+2),
    take c' = omega^a * (k+1) + omega^a' * (N-1) + pred_N (omega^a')
    where a' = pred_N a
*)


Definition Pred_omega_an : forall a k, (S k < N)%nat -> 
       lt zero a -> c = cons a (S k) zero 
          -> pred_spec c.
 intros a k Hk; intros.
 subst c.
 assert (nf a).
 eapply nf_inv1; eauto.
 assert (lt a (cons a (S k) zero)).
 apply head_lt_cons.
 assert (H23:correct N a).
 inversion coeff_ok;auto.
 pose (a' := recurr a H23 H0 H1).
 case a'.
 intros preda (H2,(H3,(H4,H5))).
 assert (lt preda a).
 case H3.
 intro; absurd (lt zero zero).
 apply lt_irr.
 case H6;intros H61 H62.
 rewrite H61 in H;auto.
 auto.
 assert (lt (cons preda 0 zero) (cons a  (S k) zero)).
 constructor 2;auto.
 assert (nf (cons preda 0 zero)).
 constructor.
  auto.
 auto with arith.
 assert (H27: correct N (cons preda 0 zero)).
 constructor.
 unfold N; auto with arith.
 auto.
 constructor.
 pose (a'' := recurr _ H27 H8 H7).
 case a''.
 intros predpred Hs.

 (* building the result *)

 exists (cons a  k (cons preda  N0 predpred)).
 case Hs;intros.
 clear Hs; case H10;intros.
 clear H10; case H12; intros; clear H12.
 case H11; intro.
 case H12; intros H121 H122.
 discriminate H121.
 split.
 generalize H9 H12;case predpred.
 constructor.
 auto.
 auto with arith.
 constructor. 
 auto.
 constructor.
 auto.
 auto.
 constructor 3.
 inversion H15.
 auto.
 inversion H17.
 inversion H17.
 auto.
 auto.
 split.
 simpl.
 right.
 constructor 3.
 auto with arith.
 split.
 simpl.
 
 rewrite H10.
 simpl.
 rewrite H4.
 assert (0 < val N a)%nat.
 unfold N.
 eapply  val_positive.
 auto.
 auto.
 Focus 2.
 constructor.
 unfold N; auto.
 inversion coeff_ok.
 auto.
 constructor.
 auto.
 auto.
 auto.
 pred_exhib H14 q.
 rewrite e.
 simpl.
 assert (0 < N ^ q)%nat.
 elim q.
 simpl.
 auto with arith.
 simpl.
 intros.
 replace 0 with (0 + 0)%nat.
 apply plus_lt_le_compat.
 auto.
 auto with arith.
 simpl; auto.

 simpl.
 pred_exhib H15 u.
 rewrite e0.
 simpl.
 ring.
Defined.





(*  if c = omega^a*(k+1)+b ,
    take c' = omega^a*(k+1)+b'
    where b' = pred_N b
*)

Definition Pred_omega_anb : forall a k b,  ((S k) < N)%nat -> 
       zero < a -> zero < b -> c = cons a   k b 
          -> pred_spec c.
 intros a k b Hk; intros.
 subst c.
 assert (nf b).
 eapply nf_inv2; eauto.
 assert (lt b (cons a k b)).
 apply tail_lt_cons. 
 auto.
 

  (* cette partie devrait etre lemifiée *)
  assert (H27: correct N b).
 inversion coeff_ok; auto.
  pose (b' := recurr b H27 H1 H2).
 
  case b'.
 
  intros predb (H2',(H3,(H4,H5))).
 assert (lt predb b).
 case H3.
 intro; absurd (lt zero zero).
 apply lt_irr.
 case H6; intros H61 H62.
 rewrite H61 in H0;auto.
 auto.
 exists (cons a  k predb).
 split.
 generalize H2' H6;case predb.
 constructor.
 eapply nf_inv1;eauto.
 auto with arith.
 intros.
 eapply nf_tail_lt_nf. 
 eauto.
 auto.
 auto.
 split.
 right.
 constructor 4.
 auto .
 split.
 Focus 2.
 constructor.
 auto.
 inversion coeff_ok. 
 auto.
 auto.
 simpl.
 rewrite H4.
 simpl.
 assert (0 < N ^ (val N a))%nat.
 generalize (val N a).
 intro n; elim n.
 simpl; auto.
 simpl;
 intros.
 replace 0 with (0 + 0)%nat.
 apply plus_lt_le_compat.
 auto. 
 auto with arith.
 simpl;auto.
 pred_exhib H7 q.
 rewrite e.
 simpl.
 assert (0 < val N b)%nat.
 unfold N;eapply  val_positive. 
 auto.
 auto.
 pred_exhib H8 r.
 rewrite e0.
 simpl.
 ring.
Defined.



Definition Pred : pred_spec c.
 generalize (refl_equal c) nf_c coeff_ok recurr; pattern c at -1; case c.
 intros.
 apply pred_n_zero.
 destruct t.
 intros.
 assert (t = zero).
 inversion_clear nf_c0.
 auto.
 inversion H1.
 inversion H0.
 subst t.
 fold (F (S n)).
 apply PredF.
 inversion coeff_ok0.
 auto with arith.
 destruct n0.
 
 destruct t.
 intro eq; case eq.
 intros.
 apply Pred_omega_a with (cons t1 n t2).
 constructor.
 auto.
 intro eq; case eq.
 intros.
 eapply Pred_omega_anb.
 4:eapply eq.
 unfold N; auto with arith.
 constructor.
 constructor.
 destruct t.
 intro eq; case eq.
 intros.
 eapply Pred_omega_an.
 3: eapply eq.
 subst c; inversion coeff_ok0.
 eauto with arith.
 constructor.
 intro eq; case eq.
 intros.
 eapply Pred_omega_anb.
 4:eapply eq.
 subst c; inversion coeff_ok0.
 auto.
 constructor.
 constructor.
Defined.

End predecessor.

(* we now use transfinite induction *)

Definition gpred : forall (N0:nat)(c:T1), correct (S (S N0)) c ->
                   nf c ->
                   pred_spec N0 c.

 intros N0 c Hc H1; pattern c.
 eapply EPSILON0.transfinite_induction_Q with (Q:= fun c => correct (S (S N0)) c).
 2:auto.
 2:auto.
 intros.
 apply Pred.
 auto.
 auto.
 auto.
Defined.

Lemma gpred_lt : 
 forall (N0 : nat) (c : T1)
        (H:correct (S (S N0)) c)
        (H': nf c), 
     match (gpred N0 c H H')
     with (exist c' _) => c = zero /\ c'=zero  \/ c' < c end.
Proof.
 intros.
 case (gpred N0 c H H');simpl.
 intros x Hx; case Hx.
 destruct 2;auto.
Qed.





Definition goodstein_next N0 c (H:nf c)
                              (H0 : correct (S (S N0)) c) :
   {c' : T1 | nf c' /\ 
                correct (S (S (S N0))) c' /\ 
                (c=zero /\ c'=zero \/ c' < c) /\
                val (S (S (S N0))) c' = 
                Peano.pred (val (S (S (S N0))) c)}.
 intros.
 assert (correct (S (S (S N0))) c).
 apply correct_succ; auto.
 case (gpred (S N0) c H1 H). 
 intros.
 exists x;auto.
 tauto.
Defined.

Definition goodstein_next_ord  N0 c (H:nf c)
                                   (H0 : correct (S (S N0)) c) : T1.
 intros.
 case (goodstein_next N0 c H H0).
 intros x Hx; exact x.
Defined.

Lemma goodstein_next_ord_lt : forall N0 c (H:nf c)
                                         (H0 : correct (S (S N0)) c),
   (c = zero /\  
    goodstein_next_ord N0 c H H0 = zero)  \/ 
       goodstein_next_ord N0 c H H0 < c.
Proof.
 unfold goodstein_next_ord;intros.
 case (goodstein_next N0 c H H0).
 intros.
 tauto.
Qed.



Lemma goodstein_next_ord_nf : forall N0 c (H:nf c)
                                          (H0 : correct (S (S N0)) c),
   nf (goodstein_next_ord N0 c H H0).
Proof.
 unfold goodstein_next_ord;intros.
 case (goodstein_next N0 c H H0).
 intros.
 tauto.
Qed.

Lemma goodstein_next_ord_correct : forall N0 c (H:nf c)
                                          (H0 : correct (S (S N0)) c),
   correct (S (S (S N0))) (goodstein_next_ord N0 c H H0).
  unfold goodstein_next_ord;intros.
 case (goodstein_next N0 c H H0).
 intros. tauto.
Qed.

Inductive Rg : (prod nat T1) -> (prod nat T1) -> Prop :=
  Rg_i : forall N0 c (H: nf c)(H0: (correct   (S (S N0)) c)),
                           Rg (N0,c)  (S N0, goodstein_next_ord N0 c H H0).
Notation  "i1 '-G->' i2" := (Rg i1 i2) (at level 70): cantor_scope.

Require Import Relations.
Notation "i1 '-G->*' i2" := (clos_refl_trans _ Rg i1 i2) (at level 70):cantor_scope.

Lemma Goodstein_decrease : forall N0 c N' c', (N0,c) -G-> (N',c') -> 
                              c = zero /\ c'=zero \/ c' < c.
Proof.
 inversion 1.
 subst c0;apply goodstein_next_ord_lt.
Qed.



Theorem Goodstein_thm : forall c , nf c -> 
                      forall N0, correct (S (S N0)) c -> {N':nat |
                         (N0,c) -G->* (N',zero)}.
Proof.
 intros  c Hc.
 pattern c;apply EPSILON0.transfinite_induction.
 2:auto.
 destruct x.
 intros ; exists N0.
 constructor 2.

 intros.
 pose (c':= goodstein_next_ord  N0 (cons x1 n x2) H H1).
 
 assert (c' < (cons  x1 n x2)).
 assert ((N0,(cons x1 n x2)) -G-> (S N0, c')).
unfold c'; constructor.
 subst c'.
case (Goodstein_decrease _ _ _ _ H2).
 destruct 1.
 discriminate H3.
 auto.
 assert (nf c').
 unfold c'; apply goodstein_next_ord_nf.
 assert (correct (S (S (S N0))) c').
 unfold c';
 apply goodstein_next_ord_correct.
 
 case (H0 c' H3 H2 (S N0) H4).
 intros.
 exists x.
 constructor 3 with (S N0, c').
 constructor 1.
 unfold c'; constructor.
 auto.
Qed.

 
 



