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
Require Import Omega.
Require Import Relations.



Record item :Set := quad {
                    base: nat ; 
                    coeff2 :nat ; (* coefficient of b² *)
                    coeff1 :nat ; (* coefficient of b *)
                    coeff0 :nat    (* coefficient of b° *) }.


(* relation between two consecutive items of the sequence *)

Inductive Rg: item -> item ->Prop :=
 Rg0 : forall b i j k, Rg (quad b i j (S k)) (quad  (S b) i j k)
|Rg1 : forall b i j , Rg (quad b i (S j) 0) (quad (S b) i j b)
|Rg2 : forall b i  , Rg (quad b (S i) 0 0)  (quad (S b) i b b).


Hint Constructors Rg.

Definition Rgstar := clos_refl_trans _ Rg.

Definition reachable (q:item) := Rgstar (quad 3 2 2 2) q.

(* We want to prove the following result :
   

Theorem G4_length : reachable
                    (quad
                      (3 * 2 ^ (3 * 2 ^ (3 ^3) + 3 ^3) - 1)
                      0
                      0
                      0).

*)


(* Let us introduce some concepts *)

Hint Unfold reachable.

Hint Constructors clos_refl_trans.

Lemma reachable_Rgstar : forall q q', reachable q -> 
                                      Rgstar q q' -> 
                                      reachable q'.
Proof.
 intros q q' H H0.
 unfold reachable; constructor 3 with q;auto.
Qed.

Inductive final : item -> Prop :=
 final_intro :forall b , final (quad b 0 0 0).

Hint Constructors final.


Lemma final_no_future : forall q, final q -> forall q', ~ Rg q q'.
Proof.
 red;intros q Hq ; elim Hq.   
 inversion 1.
Qed.

(* First, we want to explore interactively the reachable items *)

Definition next (q:item) : {q' : item | Rg q q'} + {final q}.
 intros q; case q ; intros b x y z.
 case z.
  case y.
   case x;auto.
   intro x';left;exists (quad (S b) x' b b);auto.
   intros y';left;exists (quad (S b) x y' b);auto.
   intros z'; left; exists (quad (S b) x y z');auto.
Defined.





Fixpoint nexts (n:nat)(q:item){struct n} : option item :=
  match n with 0 => Some q
             | S p => (match (next q) 
                       with  | inleft (exist q' _) =>  nexts p q'
                             | inright  _ => None
                          
                                         end)
  end.


 
Lemma next_unicity : forall q q' q'',
      Rg q q' -> Rg q q'' -> q' = q''.
Proof.
 destruct 1; inversion_clear 1;auto.
Qed.

Lemma nexts_plus : forall n p q , nexts (n+p) q = match (nexts n q)
                                                 with Some q' => nexts p q' |
                                                      None => None end.
 induction n;simpl.
 auto.
 intros; case (next q).
 intro s; case s;auto.
 auto.
Qed.


Lemma nexts_ok : forall n q q', nexts n q  = Some q' ->
                                Rgstar q q'.
Proof.
 induction n; simpl; auto.
 injection 1; destruct 1;constructor 2.
 intros q q'; case (next  q).
 destruct s.
 intro.
 constructor 3 with x;auto.
 apply IHn;auto.
 discriminate 2.
Qed.

Lemma nexts_ok_R : forall q q', Rgstar q q' ->
                              exists n, nexts n q  = Some q'.
Proof.
 intros.
 elim H.
 exists 1. 
 simpl.
 case (next x).
 intro s. 
 case s. 
 intros x0 H1.  rewrite (next_unicity _ _ _ H1 H0).
 trivial.
 intros.
 case (final_no_future _ f _ H0).
 exists 0.
 simpl;trivial.
 intros.
 case H1;case H3;intros.
 exists (x1 + x0).
 rewrite nexts_plus;auto.

 rewrite H5.
 auto.
Qed.

Definition nth_item n := nexts n (quad 3 2 2 2).

(* let us look for regularities *)

Eval compute in nth_item 0.
(*  = Some (quad 3 2 2 2)
     : option item
*)

Eval compute in nth_item 2.

(*
    = Some (quad 5 2 2 0)
     : option item
*)

Eval compute in nth_item 3.

(*
    = Some (quad 6 2 1 5)
     : option item
*)

Eval compute in nth_item 8.
(*     = Some (quad 11 2 1 0)
     : option item
*)

Eval compute in nth_item 20.
(*
     = Some (quad 23 2 0 0)
     : option item
*)

Eval compute in nth_item 21.

(*
 = Some (quad 24 1 23 23)
     : option item
*)
Eval compute in nth_item 44.
(*
  = Some (quad 47 1 23 0)
     : option item
*)
Eval compute in nth_item 92.

(*
= Some (quad 95 1 22 0)
     : option item
*)

Eval compute in nth_item 188.

(*
    = Some (quad 191 1 21 0)
     : option item 
*)


(* Eureka : 11 = 3 * 2 ^ 2 - 1
            23 = 3 * 2 ^ 3 - 1
            47 = 3 * 2 ^ 4 - 1 
            95 = 3 * 2 ^ 5 - 1
           191 = 3 * 2 ^ 6 - 1
*)


(* let us define the function f n = 3 * 2 ^ n - 1 *)

Fixpoint power (b:nat)(n:nat){struct n}:nat :=
 match n with 0 => 1
            | S p => b * b ^ p
 end
where  "n ^ p" := (power n p):nat_scope.


Definition f n := pred (3 * 2^n).

Lemma f_Sn : forall n,  f (S n) = S (2*(f n)).
 induction n;simpl.
 compute.
 auto.
 unfold f;simpl.
 unfold f at 1 in IHn.
 simpl in IHn.

 omega.
Qed.


(* we start a sequence of reachability lemmas, until we reach
  a final item of the sequence *)

  


(* A first generalization of the previous examples *)

Lemma L1 :  forall k i j b, 
      Rgstar (quad b i j (S k)) (quad (S k + b) i j 0).
Proof.
 induction k.
 simpl.
 constructor 1;auto.
 simpl.
 econstructor 3.
 econstructor 1; eauto.
 simpl in IHk.
 replace (S (S (k+b))) with (S (k + (S b))).
 apply IHk.
 auto with arith.
Qed.


Lemma L2 :  forall k i j b, 
      Rgstar (quad b i j k) (quad (k + b) i j 0).
 intro k; case k;intros.
 simpl;constructor 2.
 apply L1.
Qed.


(* hmmm, let us look at items of the form (base,i,j,0)  *)

Lemma L3 : forall b i j, 
    Rgstar (quad b i (S j) 0) (quad (S (2 * b)) i j 0).
Proof.
 intros.
 case b.
 simpl.
 econstructor 1.
 constructor.
 econstructor 3. 
 econstructor 1; econstructor.
 replace (S (2* S n)) with ( S n  + S (S n)).
 apply L1.
 omega.
Qed.

Lemma L4 :  forall b i j,
                   reachable (quad (f b) i (S j) 0) ->
                   reachable (quad (f (S b)) i j 0).
Proof.
 intros.
 econstructor 3. 
 unfold reachable in H. 
 eexact H.
 rewrite f_Sn.
 apply L3.
Qed.


Lemma L5 :  forall k b i j, 
          reachable (quad (f b) i (k+j) 0) ->
          reachable (quad (f (k+b)) i j 0).
Proof.
 induction k.
 simpl.
 auto.
 intros; econstructor 3. 
 unfold reachable in IHk; eapply IHk.
 replace (S k + j) with (k + (S j)) in H.
 unfold reachable in H;eauto.
 omega.
 simpl;rewrite f_Sn.  
 apply L3.
Qed.



Lemma F1 : reachable (quad (f 1) 2 2 0).
Proof.
 compute.
 replace 5 with (2+3).
 apply L1.
 simpl;trivial.
Qed.


Lemma F2 : reachable (quad (f 2) 2 1 0).
Proof.
 apply L4.
 apply F1.
Qed.


Lemma F3 : reachable (quad (f 3) 2 0 0).
Proof.
 compute.
 apply nexts_ok with 20.  
 trivial.
Qed.





(* Ah, ah : the second component of the current tuple becomes 1 *)

Lemma SF3 : reachable (quad (S (f 3)) 1 (f 3) (f 3)). 
Proof.
 eapply reachable_Rgstar. 
 eexact F3.
 constructor 1.
 constructor.
Qed.




Lemma F4 : reachable (quad (f 4) 1 (f 3) 0).
Proof.
 rewrite (f_Sn 3).
 eapply reachable_Rgstar.
 eexact SF3.
 replace (S (2 * (f 3))) with (f 3 + (S ( f 3))).
 apply L2.
 compute.
 trivial.
Qed.



Lemma F27 :  reachable (quad (f 27) 1 0 0).
Proof.
 replace 27 with (f 3 + 4).
 apply L5. 
 rewrite <- plus_n_O ; apply F4.
 trivial.
Qed.


(* Ok, the second component becomes 0 *)

Lemma SF27 : reachable (quad (S (f 27)) 0 (f 27) (f 27)).
Proof.
 eapply reachable_Rgstar.
 eexact F27.
 constructor 1.
 constructor.
Qed.


Lemma F28 : reachable (quad (f 28) 0 (f 27) 0).
Proof.
 rewrite f_Sn.
 replace (S (2 * f 27)) with (f 27 + (S (f 27))).
 2:omega.
 eapply reachable_Rgstar. 
 eexact SF27. 
 apply L2.
Qed.

(* yep! we are finished ! *)

Lemma Final : reachable (quad (f (f 27 + 28)) 0 0 0).
Proof.
 apply L5.
 rewrite <- plus_n_O.
 apply F28.
Qed.



(* f (f 27 + 28) = f (402653211) =  3 * 2 ^ 402653211 - 1  =

               3
             (3  )       3
       (3 x 2        + 3   )
  3 x 2                       -1
*)


Lemma big_number_eq : f (f 27 + 28) = 
          3 * 2 ^ (3 * 2 ^ (3 ^3) + 3 ^3) - 1.
Proof.
 unfold f.
 rewrite <- pred_of_minus.
 replace 27 with (3^3).
 generalize (3^3).
 intro n; assert (0 < 2 ^ n). 
 induction n.
 simpl;auto with arith.
 simpl.
 auto with arith. 
 generalize H ; generalize (2 ^n).
 intros.
 replace (pred (3*n0) + S n) with (3*n0 + n).
 auto.
 omega.
 simpl;trivial.
Qed.



Theorem G4_length : reachable
                    (quad
                      (3 * 2 ^ (3 * 2 ^ (3 ^3) + 3 ^3) - 1)
                      0
                      0
                      0).
Proof.
(* Opaque power.
 rewrite big_number_eq. *)
 generalize big_number_eq.
 generalize (3 * 2 ^ (3 * 2 ^ 3 ^ 3 + 3 ^ 3) - 1).
 generalize Final.
 generalize (f (f 27 + 28)).
 induction 2.
 auto.
Qed.



Require Import ZArith.

Open Scope Z_scope.
Definition f_Z n := 3*(Zpower 2 n)-1.

Eval compute in  (f_Z 27 + 28).

(*
   = 402653211
     : Z
*)
