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

    Yves Bertot (for AccElim3 )
*)


Section restricted_recursion.

 Variables (A:Type)(P:A->Prop)(R:A->A->Prop).

 Definition restrict (a b:A):Prop :=
   P a /\ R a b /\ P b.

 Definition well_founded_P := forall (a:A), P a -> Acc restrict a.

 Definition P_well_founded_induction_type :
       well_founded_P  ->
       forall X : A -> Type,
       (forall x : A, P x -> (forall y : A,P y-> R y x -> X y) -> X x) ->
       forall a : A, P a -> X a.
  intros W X H a.
  pattern a; eapply well_founded_induction_type with (R:=restrict).
  unfold well_founded.
  split.
  unfold well_founded_P in W.
  intros; apply W.
 case H0.
 auto.
 intros; apply H.
 auto.
 intros; apply X0.
 unfold restrict; auto.
 auto.
Defined.


End restricted_recursion.
 
Theorem AccElim3 :
forall A B C:Type,
 forall (RA:A->A->Prop)
        (RB:B->B->Prop)
        (RC:C->C->Prop),
 forall (P : A -> B -> C ->  Prop),
 (forall x y z,
    (forall (t : A), RA t x -> 
                     forall y' z', Acc RB y' -> Acc RC z' ->
                                   P t y' z') ->
    (forall (t : B), RB t y -> 
                     forall z', Acc RC z' -> P x t z') ->
    (forall (t : C), RC t z -> P x y t) -> 
    P x y z) ->
  forall x y z, Acc RA x -> Acc RB y -> Acc RC z -> P x y z.
Proof.
 intros A B C RA RB RC P H x y z Ax; generalize y z; clear y z.
 elim Ax; clear Ax x; intros x _ Hrecx y z Ay; generalize z; clear z.
 elim Ay; clear Ay y;
 intros y _ Hrecy z Az; elim Az; clear Az z; auto. 
Qed.


Theorem accElim3:
 forall (A B C:Set)(RA : A -> A ->Prop) (RB : B-> B-> Prop)
                   (RC : C -> C -> Prop)(P : A -> B -> C ->  Prop),
 (forall x y z ,
  (forall (t : A), RA t x ->  P t y z) ->
  (forall (t : B), RB t y ->  P x t z) ->
  (forall (t : C), RC t z ->  P x y t) ->  P x y z) ->
 forall x y z, Acc RA x -> Acc RB y -> Acc RC z ->  P x y z.

intros A B C RA RB RC P H x y z Ax Ay Az.
 generalize Ax Ay Az.
 pattern x, y, z;
 eapply AccElim3 with (RA:=RA)(RB:=RB)(RC:=RC) ;eauto.
 intros; apply H.

 intros;apply H0; auto.
 eapply Acc_inv;eauto.
 intros;apply H1; auto.
 eapply Acc_inv;eauto.
 intros;apply H2; auto.
  eapply Acc_inv;eauto.
Qed.



 
