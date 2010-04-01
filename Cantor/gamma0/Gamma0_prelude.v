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
    LaBRI, Universit� Bordeaux 1, and Inria Futurs (Logical)
*)

(* Veblen "pre" Normal form Basic definitions  *)


Require Import Arith.
Require Import Omega. (* ( :-) *)
Require Import Compare_dec.
Require Import Relations.
Require Import Wellfounded.
Require Import Max.

Require Import Tools.
Require Import More_nat.
Require Import AccP.
Require Import not_decreasing.
Require Import EPSILON0.
Require Import More_nat.

Set Implicit Arguments.


(************************)
(*   Definitions        *)
(************************)


(* cons a b n r is : psi(a,b)*(S n)+ r  *)

Inductive T2 : Set :=
  zero : T2
| cons : T2 -> T2  -> nat -> T2 -> T2.

Notation "[ x , y ]" := (cons x y 0 zero) (at level 0) :g0_scope.

Open Scope g0_scope.

Definition psi alpha beta  := [alpha, beta].

Definition psi_term alpha :=
  match alpha with zero => zero
                 | cons a b n c => [a, b]
  end.

Definition one  := [zero,zero].


Lemma psi_eq : forall a b, psi a b = [a,b].
Proof.
 trivial.
Qed.

Ltac fold_psi :=  rewrite <- psi_eq.
Ltac fold_psis := repeat fold_psi.


Definition finite  p := match p with 
                             0 => zero
                           | S q => cons zero zero q zero
                           end.

Notation "'F' n" := (finite n)(at level 29) : g0_scope.

Inductive is_finite:  T2 ->  Set := 
 zero_finite : is_finite zero
|succ_finite : forall n, is_finite (cons zero zero n zero).

Hint Constructors is_finite : T2.

Definition omega  := [zero,one].

Definition epsilon0  := [one,zero].

Definition epsilon alpha := [one, alpha].





(* injection from Cantor Normal Form *)

Fixpoint T1_inj (c:T1) : T2 :=
 match c with EPSILON0.zero => zero
            | EPSILON0.cons a n b => cons zero (T1_inj a) n (T1_inj b)
 end.




(* additive principals *)


Inductive ap : T2 -> Prop :=
ap_intro : forall alpha beta, ap [alpha, beta].

(* strict order on terms *)

(* Note : try to use psi as often as possible in the constructors
  premises *)

Inductive lt : T2 -> T2 -> Prop :=
| (* 1 *) 
 lt_1 : forall alpha beta n gamma,  zero < cons alpha beta n gamma
| (* 2 *)
 lt_2 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
                alpha1 < alpha2 ->
                beta1 < cons alpha2 beta2 0 zero ->
               cons alpha1 beta1 n1 gamma1 <
               cons alpha2 beta2 n2 gamma2
| (* 3 *)
 lt_3 : forall alpha1  beta1 beta2 n1 n2 gamma1 gamma2, 
               beta1 < beta2 ->
               cons alpha1 beta1 n1 gamma1 <
               cons alpha1 beta2 n2 gamma2

| (* 4 *)
 lt_4 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
               alpha2 < alpha1 ->
               cons alpha1 beta1 0 zero < beta2 ->
               cons alpha1 beta1 n1 gamma1 <
               cons alpha2 beta2 n2 gamma2

| (* 5 *)
lt_5 : forall alpha1 alpha2 beta1 n1 n2 gamma1 gamma2, 
               alpha2 < alpha1 ->
               cons alpha1 beta1 n1 gamma1 <
               cons alpha2  (cons alpha1 beta1 0 zero) n2 gamma2

| (* 6 *)
lt_6 : forall alpha1 beta1  n1  n2 gamma1 gamma2,  (n1 < n2)%nat ->
                                    cons alpha1 beta1 n1 gamma1 < 
                                    cons alpha1 beta1 n2 gamma2

| (* 7 *)
  lt_7 : forall alpha1 beta1 n1   gamma1 gamma2,  gamma1 < gamma2 ->
                                      cons alpha1 beta1 n1 gamma1 <
                                      cons alpha1 beta1 n1 gamma2
where  "o1 < o2" := (lt o1 o2): g0_scope.
Hint Constructors lt : T2.





Definition le t t' := t = t' \/ t < t'.
Hint Unfold le : T2.

Notation "o1 <= o2" := (le o1 o2): g0_scope.

Definition tail c := match c with | zero => zero 
                                  | cons a b n c => c
                             end.
(* Veblen Normal Form *)

Inductive nf : T2 -> Prop :=
| zero_nf : nf zero
| single_nf : forall a b n, nf a ->  nf b -> nf (cons a b n zero)
| cons_nf : forall a b n a' b' n' c', 
                             [a', b'] < [a, b]  -> 
                             nf a -> nf b -> 
                             nf(cons a' b' n' c')-> 
                             nf(cons a b n (cons a' b' n' c')).
Hint  Constructors nf : T2. 


Fixpoint succ (a:T2) : T2 :=
 match a with zero => finite 1
             | cons zero zero n c => finite (S (S n))
             | cons a b n c => cons a b n (succ c)
 end.


Fixpoint pred  (a:T2) : option T2 :=
 match a  with zero => None
             | cons zero zero 0 zero => Some zero
             | cons zero zero (S n) zero => 
                  Some (cons zero zero n zero)
             | cons a b n c => (match (pred c) with
                                   Some c' => Some (cons a b n c')
                                  | None => None
                                  end)
 end.

Inductive lt_epsilon0 : T2 -> Prop :=
  zero_lt_e0 : lt_epsilon0 zero 
| cons_lt_e0 : forall  b n c,   lt_epsilon0 b ->
                                lt_epsilon0 c -> 
                                lt_epsilon0 (cons zero b n c).


(* end of main definitions *)

 
