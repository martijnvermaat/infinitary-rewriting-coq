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


Require Import Ensembles.
Require Import Relations.
Set Implicit Arguments.
Section  partial_fix.

 
 Variable T : Type.
 Variable D : Ensemble T.
 Variable lt : T -> T -> Prop.
 Hypothesis  lt_D : forall x y, lt x y -> D x.
 Hypothesis gt_D : forall x y, lt x y -> D y.
 Hypothesis D_Acc : forall x, D x -> Acc lt x.

Section Acc_iterP.

  Variable P : T-> Type.

 Variable F : forall x:T, (forall y:T,  lt y x -> P y) -> D x -> P x.


 
Fixpoint Acc_iter_partial (x:T) (H:D x) (a:Acc lt x) {struct a} : P x :=
    F  (x:=x)
     (fun (y:T) (h: lt y  x) =>
          Acc_iter_partial (lt_D h) (Acc_inv a _ h))H .


End Acc_iterP.


Definition partial_fun_induction P F (x:T) Dx :=
  Acc_iter_partial P F Dx (D_Acc (x:=x) Dx).


Section FixPoint.

 Variable P : T -> Type.

 Variable F : forall x:T, (forall y:T, lt  y  x -> P y) -> D x -> P x.


 
Definition PFix (x:T)(H:D x) := Acc_iter_partial P F H (D_Acc  H).

 Hypothesis
    F_ext :
      forall (x:T) (f g:forall y:T,  lt y  x -> P y) (Dx: D x),
        (forall (y:T) (p:lt y  x), f y p = g y p) -> F f Dx = F g Dx.

Lemma PFix_F_eq :
   forall (x:T)(H:D x)(r:Acc lt x),
    F  (fun (y:T) (h: lt y x) => 
      Acc_iter_partial P F (lt_D  h) (Acc_inv  r y h))H  = 
      Acc_iter_partial P F H r.
  Proof.
   destruct r using Acc_inv_dep.
   auto.
 Qed.

  Lemma PFix_F_inv :  forall (x:T)(H:D x) (r s:Acc lt x),
       Acc_iter_partial P F H r  = Acc_iter_partial P F H s .
  Proof.
   intro x.
   intro H.
   generalize H.
   pattern x.
   apply partial_fun_induction.
   intros. 
   rewrite <- (PFix_F_eq  H2 r). 
   rewrite <- (PFix_F_eq  H2 s).
   apply F_ext.
   auto.
   auto.
  Qed.


 Lemma PFix_eq : forall (x:T )(H:D x),
             PFix  H = 
             F  (fun (y:T) (h: lt y  x) => PFix  (lt_D h)) H.
 Proof.
  intro x; unfold PFix in |- *.
  intro;rewrite <- (PFix_F_eq (x:=x)).
  apply F_ext; intros.
  apply PFix_F_inv.
Qed.

End FixPoint.




(*
Check PFix_eq.

PFix_eq
     : forall (P : T -> Type)
         (F : forall x : T, (forall y : T, lt y x -> P y) -> D x -> P x),
       (forall (x : T) (f g : forall y : T, lt y x -> P y) (Dx : D x),
        (forall (y : T) (p : lt y x), f y p = g y p) -> F x f Dx = F x g Dx) ->
       forall (x : T) (H : D x),
       PFix P F H = F x (fun (y : T) (h : lt y x) => PFix P F (lt_D h)) H

*)
End partial_fix.
