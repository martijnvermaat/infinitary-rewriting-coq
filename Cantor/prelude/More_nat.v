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

Require Import Arith.
Require Import ArithRing.
Require Import Compare_dec.
Require Import Omega.
Require Import Max.

Set Implicit Arguments.

Fixpoint power (base exp:nat){struct exp}:nat :=
  match exp with 0 => 1
               | S exp' => base * (power base exp')
  end.

Notation "n ^ p" := (power n p):nat_scope.

Lemma power_of_1 : forall p, power 1 p = 1.
 induction p; simpl.
 auto.
 rewrite IHp;auto.
Qed.
 
Goal forall a b, 0 < power (S a) b.
 induction b.
 simpl;auto.
 simpl.
 auto with arith.
Save power_positive.


Lemma pred_of_power : forall b e, pred (power (S b) (S e)) =
                                  (power (S b) e)*b  + 
                                  pred (power (S b) e).
 simpl.
 intros;generalize ((S b) ^e).
 destruct n.
 simpl.
 rewrite mult_0_r.
 simpl;auto.
 rewrite (mult_comm b (S n)).
simpl.
ring.
Qed.

(* some tools *)

(* this kind of argument must replace a lot of steps in proofs.
   must define the same for cpnf and ordinals *)



Lemma get_predecessor : forall (n:nat), 0 < n -> {p:nat | n = S p}.
 intro n; case n.
 intro ; absurd (0<0); auto with arith. 
 intro n0; exists n0;auto.
Qed.

Ltac pred_exhib H name := 
  match type of H
       with O < ?n =>
         case (get_predecessor  H); intro name; intro 
  end.




(* about euclidean division *)

Lemma Euc1 : forall b q  q' r r', 0 < b -> 
                                  q*b + r = q'*b + r' -> 
                                  r < b -> r' < b -> q = q'.
intros; case (lt_eq_lt_dec q q').
destruct 1.
assert (S q <= q').
auto with arith.
assert ((S q)*b + r <= q' *b + r).
apply plus_le_compat_r. 
apply mult_le_compat_r.
auto.
simpl in H4.
rewrite <- plus_assoc in H4.
rewrite H0 in H4.
omega.
auto.
intro.
assert (S q' <= q).
auto with arith.
assert ((S q')*b + r <= q *b + r).
apply plus_le_compat_r. 
apply mult_le_compat_r.
auto.
simpl in H4.
rewrite <- plus_assoc in H4.
rewrite H0 in H4.
omega.
Qed.

Lemma Euc2 : forall b q  q' r r', 0 < b -> 
               q*b+r = q'*b+r' -> r < b -> r' < b -> r =r'.
 intros.
 rewrite (Euc1  q q' H H0 H1 H2) in H0.
 omega.
Qed.



Lemma max_le_regR : forall n p q, p <= q -> max p n <= max q n.
  intros; case (max_dec p n).
 intro e;rewrite e.
 apply le_trans with q.
 auto.
  apply le_max_l.
 intro e;rewrite e.
 apply le_max_r.
Qed.

Lemma max_le_regL :  forall n p q, p <= q -> max n p <= max n q.
  intros; rewrite (max_comm n p);rewrite (max_comm n q).
  apply max_le_regR.
  auto.
Qed.




Lemma lt_lt_Sn : forall a b c, a < b -> b < S c -> a < c.
 eauto with arith.
Qed.




 
