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

(* Veblen "pre" Normal form (for Gamma0) *)

Require Import EPSILON0.

Require Import Arith.
Require Import List.
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
Require Import Gamma0_prelude.
Require Import Gamma0_length.

Require Import term.
Require Import rpo.

Set Implicit Arguments.

(* About nf *)

Lemma nf_a : forall a b n c, nf (cons a b n c) -> nf a.
Proof.
 inversion_clear 1;auto.
Qed.

Lemma nf_b : forall a b n c, nf (cons a b n c) -> nf b.
Proof.
 inversion_clear 1;auto.
Qed.

Lemma nf_c : forall a b n c, nf (cons a b n c) -> nf c.
Proof.
 inversion_clear 1;auto with T2.
Qed.

Hint Resolve nf_a nf_b nf_c : T2.



Ltac nf_inv := ((eapply nf_a; eassumption)|| 
                (eapply nf_b; eassumption)|| 
                (eapply nf_c; eassumption)).


(* About lt *)


Lemma zero_lt_succ : forall alpha, zero < succ alpha.
Proof.
 destruct  alpha;simpl.
 auto with T2.
 case alpha1;case alpha2;auto with T2.
Qed.


Lemma not_lt_zero : forall alpha, ~ alpha < zero. 
Proof.
 red; inversion 1.
Qed.


Lemma lt_irr : forall alpha, ~ alpha < alpha.
Proof.
 induction alpha.
 apply not_lt_zero. 
 red; inversion_clear 1.
 case (IHalpha1 H0).
 case (IHalpha2 H0).
 case (IHalpha1 H0).
 case (IHalpha1 H0).
 case (Arith.Lt.lt_irrefl _ H0).
 case IHalpha3; auto.
Qed.


Ltac lt_clean := 
  try (match goal with 
        [ineq : lt ?a zero |- _ ] => case (not_lt_zero ineq);auto
       |[ineq : Peano.lt ?a 0 |- _ ] => case (lt_n_O a);auto
       |[ref : lt ?a ?a |- _] => case (lt_irr ref);auto
       |[ref : Peano.lt ?a ?a |- _] => case (lt_irr ref);auto
  end).


Lemma le_zero_alpha : forall alpha, zero <= alpha.
Proof.
 intro alpha; case alpha; auto with T2.
Qed.

Lemma psi_le_cons : forall alpha beta n gamma,
                       [alpha, beta] <=  cons alpha beta n gamma.
Proof.
  intros;case n; auto with arith T2.
 case gamma;auto with arith T2.
Qed.

Hint Resolve psi_le_cons le_zero_alpha: T2.

Lemma le_psi_term_le : forall alpha beta, alpha <= beta ->
                                          psi_term alpha <= psi_term beta.
Proof.
 destruct 1.
 subst beta;auto with T2.
 generalize H;case alpha;simpl.
 auto with T2.
 case beta.
 intros;lt_clean.
 simpl;inversion_clear 1; auto with T2.  
Qed.


Lemma le_inv_nc : forall a b n c  n' c',
    cons a b n c <= cons a b n' c' -> (n<n')%nat \/ n=n' /\ c<= c'.
Proof.
 inversion_clear 1.
 injection H0;intros;right;auto with T2.
 inversion_clear H0; try lt_clean;auto with T2.
Qed.


Lemma lt_than_psi : forall a b n c a' b',
      cons a b n c < [a',b'] ->
      [a,b]<[a',b']. 
Proof.
 inversion_clear 1;try lt_clean;auto with T2.
Qed.


(* in order to establish trichotomy, we first use a measure on pair of
    terms *)
Section lemmas_on_length.
Open Scope nat_scope.
 
Lemma tricho_lt_2 : forall a1 a2 b1 b2 n1 n2 r1 r2,
    length a1 + length a2 < 
    length (cons a1 b1 n1 r1) +
    length (cons a2 b2 n2 r2).
Proof.
 intros.
 apply plus_lt_compat; apply length_a. 
Qed.


Lemma tricho_lt_2' : forall a1 a2 b1 b2 n1 n2 r1 r2,
    length b1 + length (cons a2 b2 0 zero)  < 
    length (cons a1 b1 n1 r1) +
    length (cons a2 b2 n2 r2).
 intros;apply plus_lt_le_compat.
 apply length_b.
 simpl.
 intros; apply le_lt_n_Sm.
 match goal with 
   [ |- ?a <= ?b + ?c + ?d] => rewrite (plus_comm (b + c) d) end.
 apply le_plus_trans.
 replace (Max.max (length b2) 0) with (length b2).
 generalize (Max.max_dec (length a2) (length b2)).
 destruct 1.
 rewrite  e.
 repeat rewrite plus_0_r.
 apply plus_le_compat.
 apply le_max_l.
 apply le_max_l.
 repeat rewrite plus_0_r.
 apply plus_le_compat;
 apply  max_le_regL;
 apply le_max_l.
 rewrite max_l; auto with arith.
Qed.



Lemma tricho_lt_3 : forall a1 a2 b1 b2 n1 n2 r1 r2,
    length b1 + length b2  <   
     length (cons a1 b1 n1 r1) +  length (cons a2 b2 n2 r2).

 intros;apply plus_lt_compat; apply length_b.
Qed.


Lemma tricho_lt_4 : forall a1 a2 b1 b2 n1 n2 r1 r2,
    length a2 + length a1 < 
    length (cons a1 b1 n1 r1) +
    length (cons a2 b2 n2 r2).
Proof.
 intros.
 rewrite plus_comm.
 apply plus_lt_compat; apply length_a. 
Qed.

Lemma tricho_lt_4' : forall a1 a2 b1 b2 n1 n2 c1 c2,
    length (cons a1 b1 0 c1) + length b2  < 
    length (cons a1 b1 n1 c1) +
    length (cons a2 b2 n2 c2).
 intros; apply plus_le_lt_compat.
 case n1.
 auto. 
 intros;apply lt_le_weak;apply length_n; auto with arith.
 apply length_b.
Qed.

Lemma tricho_lt_5 : forall a1 a2 b1  n1 n2 c1 c2,
    length a2 + length a1  < 
    length (cons a1 b1 n1 c1) +
    length (cons a2 (cons a1 b1 0 zero)  n2 c2).
 intros; rewrite plus_comm;apply plus_lt_compat; apply length_a.
Qed.

Lemma tricho_lt_7 : forall a1 b1  n1  c1 c2,
    length c1 + length c2 < 
    length (cons a1 b1 n1 c1) +
    length (cons a1 b1 n1 c2).
Proof.
 intros.
 apply plus_lt_compat;
 apply length_c. 
Qed.


End lemmas_on_length.

Hint Resolve tricho_lt_7 tricho_lt_5 tricho_lt_4 tricho_lt_4' tricho_lt_3 tricho_lt_2 tricho_lt_2 : T2.


Lemma tricho_aux : forall l, forall t t', (length t + length t' < l)%nat  ->
                    { t < t'}+{t = t'}+{t'<  t}.
Proof.
 induction l.
 intros. 
 elimtype False. 
 inversion H.
 intros t t'.
 case t;case t'.
 left;right;auto with T2.
 left;left;constructor.
 right;constructor.
 intros.
 assert (length t3 + length t0 < l)%nat.
 eapply lt_lt_Sn.
 eapply tricho_lt_2.
 eauto with T2.
 case (IHl _ _ H0).
 destruct 1.
 assert (length t4 + length (cons t0 t1 0 zero) < l)%nat.
 eapply lt_lt_Sn.
 eapply tricho_lt_2'.
 eauto.
 case (IHl _ _ H1).
 destruct 1.
 left;left.
 constructor 2;auto with T2.
 subst t4.
 right.
 constructor 5;auto with T2.
 intro.
 right.
 constructor 4;auto with T2.
 subst t3.
 assert (length t4 + length t1 < l)%nat.
  eapply lt_lt_Sn.
  eapply tricho_lt_3.
  eauto with T2.
  case (IHl _ _ H1).
 destruct 1.
 left;left. 
 constructor 3. 
 auto with T2.
 subst t4.
 case (lt_eq_lt_dec n0 n).
 destruct 1.
 left;left.
 constructor 6.
 auto with T2.
 subst n.
 assert (length t5 + length t2 < l)%nat.
 eapply lt_lt_Sn.
 eapply tricho_lt_7.
 eauto with T2.
 case (IHl _ _ H2).
 destruct 1.
 left;left.
 constructor 7;auto with T2.
 subst t2.
 left;right;trivial.
 intro.
 right;constructor 7;auto with T2.
 right.
 constructor 6;auto with T2.
 intro.
 right;constructor 3;auto with T2.
 intro.
 assert  (length t1 + length (cons t3 t4 0 zero) < l)%nat.
 eapply lt_lt_Sn.
 eapply tricho_lt_2'.
 rewrite plus_comm.
 eauto with T2.
 case (IHl _ _ H1).
 destruct 1.
 right.
 constructor 2;auto with T2.
 subst t1.
 left;left;constructor 5;auto with T2.
 left;left;constructor 4;auto with T2.
Defined.


Definition trichotomy_inf : forall t t', {t < t'}+{t=t'}+{t'<  t}.
 intros t t'.
 eapply tricho_aux.
 eapply lt_n_Sn.
Defined.


Definition lt_ge_dec : forall t t', {t<t'}+{t'<=t}.
 intros t t'; case (trichotomy_inf t t').
 destruct 1 ;[left;auto with T2| right;auto with T2].
 auto with T2.
Defined.

(* we should replace the following definition by a direct one
  by fixpoint (structural argument : sum of lengths)
  It will make the proof of compare_reflect quite harder
*)

Definition compare : T2 -> T2 -> comparison.
 intros t1 t2.
 case (trichotomy_inf t1 t2).
 destruct 1.
 exact Lt.
 exact Eq.
 intro; exact Gt.
Defined.


(* introduces an hypothesis Hname for t < t', t = t', and t' < t
    (3 subgoals) *)

Ltac tricho t t' Hname := case (trichotomy_inf t t');
                           [intros [Hname|Hname] | intro Hname].


Section trans_proof.
 Variables a1 b1 c1 a2 b2 c2 a3 b3 c3:T2.
 Variables n1 n2 n3:nat.

 Hypothesis H12 : cons a1 b1 n1 c1 <  cons a2 b2 n2 c2.
 Hypothesis H23 : cons a2 b2 n2 c2 <  cons a3 b3 n3 c3.

 Hypothesis induc : forall t t' t'', 
                     (length t + length t' + 
                     length t'' < 
                     length (cons a1 b1 n1 c1) +
                     length (cons a2 b2 n2 c2) + 
                     length (cons a3 b3 n3 c3))%nat  ->
                     lt t t' -> lt t' t'' -> lt t t''.



 Lemma trans_aux :  cons a1 b1 n1 c1 < cons a3 b3 n3 c3.
 Proof .
 inversion H12.
 inversion H23.
 constructor 2.
 apply induc with a2.
 generalize (length_a  a1 b1 n1 c1).
 generalize (length_a  a2 b2 n2 c2).
 generalize (length_a  a3 b3 n3 c3).
 clear induc.
 omega.
 auto with T2.
 auto with T2.
 assert (lt (cons a2 b2 0 zero) (cons a3 b3 0 zero)).
 auto with T2.
 apply induc with (cons a2 b2 0 zero).
 generalize (length_b  a1 b1 n1 c1).
 generalize (length_psi a2 b2 n2 c2).
 generalize (length_psi a3 b3 n3 c3).
 clear induc.
 omega.
 auto with T2.
 auto with T2.
 subst a3.
 constructor 2.
 auto with T2.
 apply induc with (cons a2 b2 0 zero).
 2:auto with T2.
 
 2:constructor 3;auto with T2.
 generalize (length_b a1 b1 n1 c1); generalize (length_psi a2 b2 n2 c2);
  generalize (length_psi a2 b3 n3 c3);clear induc;omega.
 tricho a1 a3 H20.
 constructor 2.
 auto with T2.
 apply induc with (cons a2 b2 0 zero).
 2:auto with T2.
 generalize (length_b a1 b1 n1 c1);generalize(length_psi a2 b2 n2 c2);
 generalize (length_psi a3 b3 n3 c3);clear induc;omega.
 constructor 4; auto with T2.
 clear H;subst a1.
 constructor 3.
 apply induc with (cons a2 b2 0 zero);eauto with T2.
 generalize (length_b a3 b1 n1 c1); 
generalize (length_b a3 b3 n3 c3); 
generalize (length_psi a2 b2 n2 c2);clear induc;omega. 
 constructor 4.
 auto with T2.
 apply induc with (cons a2 b2 0 zero);eauto with T2.
  generalize (length_psi a1 b1 n1 c1); 
generalize (length_psi a2 b2 n2 c2); 
generalize (length_b a3 b3 n3 c3);clear induc;omega.
tricho a1 a3 H20.
constructor 2;auto with T2.
 apply induc with  (cons a2 b2 0 zero);eauto with T2.
 subst b3.
generalize (length_b a1 b1 n1 c1); 
generalize (length_psi a2 b2 n2 c2); 
generalize (length_psi a3 (cons a2 b2 0 zero) n3 c3);
 clear induc;omega. 
clear H15 H9 H11 H17 H18 ;subst a3.
constructor 3.
auto with T2.
 constructor 4;auto with T2.
 clear H9 H11 H4 H5.
 subst a3; subst b3.
 constructor 2;auto with T2.
 clear H9 H11 H4 H5.
 subst a3;subst b3.
 constructor 2;auto with T2.
 clear H H1 H2 H3 H5 H6 H7.
 clear beta1 beta2 gamma1 gamma2.
 inversion H23.
 constructor 2;auto with T2.
 apply induc with b2;auto with T2.
generalize (length_b a1 b1 n1 c1); 
generalize (length_b a2 b2 n2 c2); 
generalize (length_psi a3 b3 n3 c3);clear induc;omega. 
constructor 3;auto with T2.
eapply induc with b2;auto with T2.
generalize (length_b a1 b1 n1 c1); 
generalize (length_b a2 b2 n2 c2); 
generalize (length_b a3 b3 n3 c3);clear induc;omega. 
constructor 4;auto with T2.
apply induc with (cons a2 b2 0 zero);auto with T2.
pattern a2 at 1;rewrite <- H4.
generalize (length_psi a1 b1 n1 c1); 
generalize (length_psi a2 b2 n2 c2); 
generalize (length_b a3 b3 n3 c3);clear induc;omega. 
clear H;subst a2.
constructor 4;auto with T2.
rewrite <- H7.
constructor 3;auto with T2.
rewrite <- H7.
constructor 3;auto with T2.
inversion H23;auto with T2.

assert (lt (cons a1 b1 0 zero) (cons a3 b3 0 zero)).
 apply induc with b2. 
   generalize (length_psi  a1 b1 n1 c1).
  generalize (length_b a2 b2 n2 c2).
  generalize (length_psi a3 b3 n3 c3);
 clear induc;
 omega.

 auto with T2.
 auto with T2.
inversion_clear H20;auto with T2.
inversion H21.
inversion H21.
subst a3.
constructor 4.
auto with T2.
apply induc with b2.
generalize (length_psi a1 b1 n1 c1);
generalize (length_b a2 b2 n2 c2);
generalize (length_b a2 b3 n3 c3);clear induc;omega.
auto with T2.
auto with T2.
 constructor 4.
 apply induc with a2.
 generalize (length_a a1 b1 n1 c1);
generalize (length_a a2 b2 n2 c2);
generalize (length_a a3 b3 n3 c3);clear induc; omega.
 auto with T2.
 auto with T2.
apply induc with (cons a2 b2 0 zero).
  generalize (length_psi a1 b1 n1 c1);
generalize (length_psi a2 b2 n2 c2);
generalize (length_b a3 b3 n3 c3);clear induc; omega.

 auto with T2.
auto with T2.

constructor 4.
apply induc with a2;auto with T2.

  generalize (length_a a1 b1 n1 c1); 
generalize (length_a a2 b2 n2 c2); 
generalize (length_a a3 b3 n3 c3);clear induc;omega.
constructor 4;auto with T2.


clear H9 H11; subst b3; subst a3.

constructor 4.
auto with T2.
auto with T2.

clear H9 H11;subst b3;subst a3.
constructor 4;auto with T2.
subst b2.
inversion H23;auto with T2.
inversion_clear H17;auto with T2.
inversion H18.
inversion H18.
subst a3.
constructor 4;auto with T2.

constructor 4;auto with T2.
apply induc with a2;auto with T2.

 generalize (length_a a1 b1 n1 c1); 
generalize (length_a a2 (cons a1 b1 0 zero) n2 c2); 
generalize (length_a a3 b3 n3 c3);clear induc;omega.

 apply induc with (cons a2 (cons a1 b1 0 zero) 0 zero);auto with T2.


 
 generalize (length_psi  a1 b1 n1 c1); 
generalize (length_psi a2 (cons a1 b1 0 zero) n2 c2); 
generalize (length_b a3 b3 n3 c3) ;clear induc;omega.
 constructor 4.
apply induc with a2;auto with T2.




 generalize (length_a a1 b1 n1 c1); 
generalize (length_a a2 (cons a1 b1 0 zero) n2 c2); 
generalize (length_a a3 b3 n3 c3);clear induc;omega.
constructor 5;auto with T2.
subst a3.
constructor 5.
auto with T2.
subst a3.
constructor 5;auto with T2.
subst a2; subst b2.
inversion H23;auto with T2.
subst a3;subst b3.
constructor 6.
eauto with T2 arith.
subst b3;subst a3;subst n3.
constructor 6;auto with T2.

clear H H1;subst a1;subst b1.
subst n2.
inversion H23;auto with T2.
constructor 7.
apply induc with c2;auto with T2.
  generalize (length_c a2 b2 n1 c1); 
generalize (length_c a2 b2 n1 c2); 
generalize (length_c a3 b3 n3 c3);clear induc;omega.

Qed.


End trans_proof.

Lemma transitivity0 : forall n, 
             forall t1 t2 t3, 
                (length t1 + length t2 + length t3  < n)%nat -> 
                 lt t1 t2 -> lt t2 t3 ->  lt t1 t3.
Proof.
 induction n.
 inversion 1.
 destruct t1; destruct t2; destruct t3.
 inversion 1.
 inversion 1.
 inversion 2.
 auto with T2.
 inversion 3.
 auto with T2.
 inversion 2.
 inversion 3.
 2:inversion 3.
 inversion H0.
 intros.
 eapply trans_aux.
 eexact H0.
 auto with T2.
 intros.
 apply IHn with t'.
 omega.
 auto with T2.
 auto with T2.
Qed.
 
Theorem transitivity : 
             forall t1 t2 t3, t1 < t2 -> t2 < t3 -> t1 < t3.
Proof.
 intros;
 apply transitivity0 with (S (length t1 + length t2 + length t3)) t2;
 auto with T2 arith.
Qed.

Theorem le_lt_trans : forall alpha beta gamma, alpha <= beta -> 
                                               beta < gamma -> 
                                               alpha < gamma.
Proof.
 destruct 1.
 subst alpha;auto with T2.
 intros; eapply transitivity;eauto with T2.
Qed.


Theorem  lt_le_trans : forall alpha beta gamma, alpha < beta ->
                                                beta <= gamma -> 
                                                alpha < gamma.
 destruct 2.
 subst beta;auto with T2.
 eapply transitivity;eauto with T2.
Qed.

Theorem le_trans : forall alpha beta gamma, alpha <= beta ->
                                            beta <= gamma ->
                                            alpha <= gamma.
Proof.
 destruct 1.
 subst beta;auto.
 intros;right;eapply lt_le_trans;eauto.
Qed.

Lemma psi_relevance : forall alpha beta n gamma  alpha' beta' n' gamma',
        [alpha, beta] <  [alpha', beta'] ->
        cons alpha beta n gamma <  cons alpha' beta' n' gamma'.
Proof.
 inversion 1.
 constructor 2;auto with T2.
 constructor 3;auto with T2.
 constructor 4;auto with T2.
 constructor 5;auto with T2.
 inversion H1.
 lt_clean. 
Qed.

Lemma nf_inv_tail : forall a b n c , nf (cons a b n c) ->
                                        c < [a,b].
Proof.
  inversion_clear 1.
  auto with T2.
  apply psi_relevance;auto with T2.
Qed.


Theorem lt_beta_psi : forall beta alpha, beta < [alpha, beta].
 induction beta.
 auto with T2.
 intros.
 cut  (beta2 < [alpha, (cons beta1 beta2 n beta3)]).
 intro H.
 tricho beta1 alpha H0.
 auto with T2.
 subst alpha.
  constructor 3.
 apply lt_le_trans with [beta1, beta2];auto with T2.
 case (psi_le_cons beta1 beta2 n beta3).
 intro.
 pattern (cons beta1 beta2 n beta3) at 2.
 rewrite <- H1.
 unfold psi;constructor 5;auto with T2.
 unfold psi; constructor 4;auto with T2.
 assert ([alpha, beta2] < [alpha, (cons beta1 beta2 n beta3)]).
  constructor 3. 
 apply lt_le_trans with [beta1, beta2]; auto with T2.
  eapply transitivity;eauto with T2.
Qed.


Lemma lt_beta_cons :  forall alpha beta n gamma, 
                            beta < cons alpha beta n gamma.
Proof.
 intros;eapply lt_le_trans.
 2:eapply psi_le_cons.
 apply lt_beta_psi.
Qed.



Theorem lt_alpha_psi : forall alpha beta, alpha < [alpha, beta].
Proof.
 induction alpha.
 unfold psi;auto with T2.
 intros.
 constructor 2.
 apply lt_le_trans with [alpha1,alpha2];auto with T2.
  apply lt_le_trans with [ alpha1,alpha2];auto with T2.
 apply lt_beta_psi.
 right;constructor 2.
 apply lt_le_trans with [alpha1,alpha2];auto with T2.
 apply lt_le_trans with [ alpha1,alpha2];auto with T2.
 apply lt_beta_psi.
 right.
 constructor 2.
  apply lt_le_trans with [ alpha1,alpha2];auto with T2.
 apply transitivity with [alpha2, beta];auto with T2.
 constructor 2.
 apply lt_beta_cons.
 apply lt_beta_psi.
Qed.


Lemma lt_alpha_cons :  forall alpha beta n gamma, 
                            alpha < cons alpha beta n gamma.
Proof.
 intros;eapply lt_le_trans.
 2:eapply psi_le_cons.
 apply lt_alpha_psi.
Qed.

Hint Resolve lt_beta_cons lt_alpha_cons : T2.



Lemma le_cons_tail : forall alpha beta n gamma gamma', gamma <= gamma' -> 
                                cons alpha beta n gamma <= 
                                cons alpha beta n gamma'.
 destruct 1.
 subst gamma';left;auto with T2.
 right;auto with T2.
Qed.


(* terms in normal form *)

Lemma nf_omega : nf omega.
 compute; auto with T2.
Qed.

Lemma nf_epsilon0 : nf epsilon0.
 compute.
 auto with T2.
Qed.

Lemma nf_epsilon : forall alpha, nf alpha -> nf (epsilon alpha).
Proof.
 intros; compute; auto with T2. 
Qed.



 
Lemma ordinal_finite : forall n, nf (finite n).
 destruct n; compute;auto with T2.
Qed.

Lemma nf_finite_inv : forall gamma n, nf (cons zero zero n gamma) -> 
                     gamma = zero.
 inversion 1;auto with T2.
 inversion H4; lt_clean; auto with T2.
Qed.



Lemma lt_tail0: forall c, nf c -> c <> zero -> tail c < c.     
Proof.
 induction c.
 destruct 2;auto with T2.
 simpl.
 generalize IHc3; case c3.
 auto with T2.
 intros.
 apply psi_relevance.
 inversion_clear H.
 auto with T2.
Qed.


Lemma lt_tail: forall a b n c, nf (cons a b n c) ->  c < cons a b n c. 
Proof.
 intros. 
 replace c with (tail (cons a b n c)). 
 apply lt_tail0.
 simpl;auto with T2.
 discriminate. 
 trivial. 
Qed.


Inductive subterm : T2 -> T2 -> Prop :=
 | subterm_a : forall a b n c, subterm a (cons  a b n c)
 | subterm_b : forall a b n c, subterm b (cons a b n c)
 | subterm_c : forall a b n c, subterm c (cons a b n c)
 | subterm_trans : forall t t1 t2, subterm t t1 -> subterm t1 t2 ->
                                                   subterm t t2.

Lemma nf_subterm : forall alpha beta, subterm alpha beta ->
                                       nf beta -> 
                                       nf alpha.
Proof.
 induction 1; intros; try nf_inv.
 auto.
Qed.



Theorem subterm_lt : forall alpha beta, subterm alpha beta -> nf beta ->
     alpha < beta.
Proof.
  induction 1;auto with T2.
  intro;apply lt_tail;auto with T2.
  intro; apply transitivity with t1;auto with T2.
 eapply IHsubterm1. 
 eapply nf_subterm;eauto with T2.
Qed.


Ltac subtermtac :=
 match goal with 
[|- subterm ?t1 (cons ?t1 ?t2 ?n ?t3)] =>
                                              constructor 1
 | [|- subterm ?t2 (cons ?t1 ?t2 ?n ?t3)] =>
                                              constructor 2
 | [|- subterm ?t3 (cons ?t1 ?t2 ?n ?t3)] =>
                                              constructor 3
| [|- subterm ?t4 (cons ?t1 ?t2 ?n ?t3)] =>
  ((constructor 4 with t1; subtermtac)     ||
 (constructor 4 with t2; subtermtac)       ||
 (constructor 4 with t3; subtermtac))
    end.

Lemma le_one_cons : forall a b n c, one <= cons a b n c.
Proof.
 unfold one.
 intros. apply le_trans with [a,b];auto with T2.
 case a; case b; auto with T2.
Qed.

Hint Resolve le_one_cons : T2.
Lemma finite_lt_omega : forall n, finite  n <  omega.
Proof.
  destruct n;compute;auto with T2.
Qed.

Lemma omega_lt_epsilon0 : omega <  epsilon0.
Proof.
 compute; auto with T2.
Qed.

Lemma omega_lt_epsilon : forall alpha, omega < epsilon alpha.
Proof.
 compute;auto with T2.
Qed.


Lemma lt_one_inv : forall alpha, alpha < one -> alpha = zero.
Proof.
 inversion 1; lt_clean.
 auto with T2.
Qed.


Lemma lt_cons_omega_inv : forall alpha beta n gamma, 
   cons alpha beta n gamma < omega ->
   nf (cons alpha beta n gamma) ->
   alpha = zero /\ beta = zero /\ gamma = zero.
Proof.
 inversion_clear 1; lt_clean.
 replace beta with zero.
 inversion 1; lt_clean;auto with T2.
  inversion  H5; lt_clean.
 inversion H0;lt_clean;auto with T2.
 inversion H1; lt_clean;auto with T2.
Qed.


Lemma lt_omega_inv : forall alpha, nf alpha -> alpha < omega ->
                        {n:nat | alpha = finite n}.
Proof.
 intros a; case a.
 exists 0;simpl.
 auto with T2.
 intros.
 case (lt_cons_omega_inv H0);auto with T2.
 destruct 2;intros.
 exists (S n);auto with T2.
 simpl.
 subst t;subst t1;subst t0; auto with T2.
Qed.

Lemma lt_omega_is_finite : forall alpha, nf alpha -> alpha < omega -> 
                                         is_finite alpha.
Proof.
 intros alpha N_alpha H; case (lt_omega_inv N_alpha H).
 destruct x; intro e;rewrite e; simpl; constructor.
Qed.

 


Theorem lt_compat : forall n p, finite n <  finite p -> 
                               (n < p)%nat.
Proof.
 destruct n;simpl.
 destruct p.
 inversion 1.
 auto with T2 arith.
 destruct p;simpl.
 inversion 1.
 inversion_clear 1;try lt_clean;auto with arith T2.
Qed.


Theorem lt_compatR : forall n p, (n <p)%nat -> 
                     finite n <  finite p .
Proof.
 destruct n;simpl.
 destruct p.
 inversion 1.
 simpl;auto with T2.
 destruct p.
 intros;lt_clean.
 simpl; auto with arith T2.
Qed.

Lemma finite_is_finite : forall n, is_finite (F n).
Proof.
 destruct n;simpl;constructor.
Qed.

Lemma is_finite_finite : forall alpha, is_finite alpha ->
                                     {n : nat | alpha = F n}.
Proof.
 destruct 1.
 exists 0;simpl;auto with T2.
 exists (S n);simpl;auto with T2.
Qed.



(* the following proof won't be so trivial, when compare is
    defined directly !!! *)

Lemma compare_reflect : forall c c', match compare c c' with
                                    |   Lt => c < c' 
                                    |   Eq => c = c'
                                    |   Gt => c' <  c
                                    end.
Proof.
 unfold compare.
 intros; case (trichotomy_inf c c');auto.
 destruct s;auto with T2.
Qed.


Lemma compare_lt_rw : forall alpha beta, compare alpha beta = Lt -> 
                                         alpha < beta.
Proof.
 intros alpha beta; generalize (compare_reflect alpha beta).
 case (compare alpha beta);(try discriminate 2; auto with T2).
Qed.


Lemma compare_eq_rw : forall alpha beta, compare alpha beta = Eq -> 
                                         alpha = beta.
Proof.
 intros alpha beta; generalize (compare_reflect alpha beta).
 case (compare alpha beta);(try discriminate 2; auto with T2).
Qed.

Lemma compare_gt_rw : forall alpha beta, compare alpha beta = Gt ->  
                                         beta < alpha.
Proof.
 intros alpha beta; generalize (compare_reflect alpha beta).
 case (compare alpha beta);(try discriminate 2; auto with T2).
Qed.

Implicit Arguments compare_gt_rw [alpha beta].
Implicit Arguments compare_lt_rw [alpha beta].
Implicit Arguments compare_eq_rw [alpha beta].


Hint Resolve compare_eq_rw compare_lt_rw compare_gt_rw.

Lemma compare_rw_lt : forall alpha beta, alpha < beta ->
                    compare alpha beta = Lt.
Proof.
 intros; generalize (compare_reflect alpha beta). 
 case (compare alpha beta).
 intro;subst beta;case (lt_irr H);auto with T2.
 auto .
 intro; case (lt_irr (alpha:=alpha)).
 eapply transitivity;eauto with T2.
Qed.

Lemma compare_rw_eq : forall alpha beta, alpha = beta ->
                    compare alpha beta = Eq.
intros; generalize (compare_reflect alpha beta). 
case (compare alpha beta).
auto with T2.
intro H0;subst beta;case (lt_irr H0).
intro H0;subst beta;case (lt_irr H0).
Qed.

Lemma compare_rw_gt : forall alpha beta, beta < alpha ->
                    compare alpha beta = Gt.
intros; generalize (compare_reflect alpha beta). 
case (compare alpha beta).
intro H0;subst beta;case (lt_irr H).
intro; case (lt_irr (alpha:=alpha)).
eapply transitivity;eauto with T2.
auto with T2.
Qed.




(* plus is defined here, because it requires decidible comparison *)

Fixpoint plus (t1 t2 : T2) {struct t1}:T2 :=
  match t1,t2 with
 |  zero, y  => y
 |  x, zero => x
 |  cons a b n c, cons a' b' n' c' =>
      (match compare (cons a b 0 zero)
                        (cons a' b' 0 zero)
                             with | Lt => cons a' b' n' c'
                                  | Gt =>
                                       (cons a b n
                                              (c +
                                                 (cons a' b' n' c')))
                                  | Eq  => (cons a b (S(n+n')) c')
       end)
 end
where "alpha + beta" := (plus alpha beta): g0_scope.


Lemma plus_alpha_0 : forall alpha,  alpha + zero = alpha.
Proof.
 intro alpha; case alpha ;trivial.
Qed.



Lemma lt_succ : forall a,  a < succ a.
 induction a;simpl;auto with T2.
 case a1;auto with arith T2.
 case a2; auto with arith T2.
Qed.

Theorem lt_succ_le : forall a b,  a < b -> 
                                         nf b -> 
                                         succ a <= b.
Proof.
  induction a.
  inversion 1.
  simpl.
  auto with T2.
  generalize IHa3; case a1; case a2.
 simpl.
 inversion 2.
right; constructor 2.
 auto with T2.
 auto with T2.
 right;constructor 3;auto with T2.
 lt_clean.
 lt_clean.

 inversion H5.

 case gamma2.
 left;auto with T2.
 right;auto with T2.
 right;constructor 6.
 auto with arith T2.
 Focus 2.
 simpl.
 intros. 
 inversion H.
 right;constructor 2;auto with T2.
 right;constructor 3;auto with T2.
 inversion H5.
 inversion H5.
 inversion H6.
 inversion H6.
 inversion H6.
 
 
 right;constructor 6.
 auto with arith T2.
 
 right;constructor 6.
 auto with arith T2.

 apply le_cons_tail.
 apply IHa0.
 auto.
 subst b.
 inversion H0;auto with T2.
 inversion 1.
 subst gamma2.
 inversion H5.
 inversion H11.
 inversion H17.
 inversion H16.
 inversion H24.
 inversion H16.
 inversion H16.

 simpl.
 intros.
  inversion H.
 right;constructor 2;auto with T2.
 right;constructor 3;auto with T2.
 right;constructor 4.
 auto.
 auto.
 right;constructor 5;auto with T2.
 right;constructor 6;auto with T2.
 Unfocus.
 Focus 2.
 intros.
 simpl.
 inversion H.
 right;constructor 2;auto with T2.
 right;constructor 3;auto with T2.
 right;constructor 4;auto with T2.
 right;constructor 5;auto with T2.
 right; constructor 6;auto with T2. 
apply le_cons_tail;auto with T2.
 auto with T2.
 auto with T2.
 apply IHa0;auto with T2.
 subst b.
 inversion H0.
 constructor.
 auto with T2.
 apply le_cons_tail;auto with T2.
  apply IHa0;auto with T2.
  subst b.
 inversion H0.
 constructor.
 auto with T2.
Qed.





  
Lemma succ_lt_le : forall a b, nf a -> nf b -> a < succ b -> a <= b. 
 intros.
 tricho a b H2; auto with T2.
 generalize (lt_succ_le H2 H).
 intro.
 case (lt_irr (alpha:=succ b)).
 eapply le_lt_trans;eauto with T2.
Qed.


Lemma succ_of_cons : forall a b n c, zero< a \/ zero< b ->
                       succ (cons a b n c)= cons a b n (succ c).
Proof.
 destruct a;destruct b;simpl;auto with T2.
 destruct 1 as [H|H];inversion H.
Qed.


(* Well foundation *)
Module  Gamma0_sig <: Signature.



Inductive symb0 : Set := nat_0 | nat_S | ord_zero | ord_psi | ord_cons.

Definition symb := symb0.

Lemma eq_symbol_dec : forall f1 f2 : symb, {f1 = f2} + {f1 <> f2}.
Proof.
 intros; decide equality.
Qed.

(** The arity of a symbol contains also the information about built-in theories as in CiME *)
Inductive arity_type : Set :=
  | AC : arity_type
  | C : arity_type
  | Free : nat -> arity_type.

Definition arity : symb -> arity_type :=
  fun f => match f with
                  | nat_0 => Free 0
                  | ord_zero => Free 0
                  | nat_S => Free 1
                  | ord_psi => Free 2
                  | ord_cons => Free 3
                  end.

End Gamma0_sig.



(** * Module Type Variables. 
 There are almost no assumptions, except a decidable equality. *) 
Module Vars <: Variables.

Inductive empty_set : Set := .
Definition var := empty_set.

Lemma eq_variable_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
Proof.
intros; decide equality.
Qed.

End Vars.

Module  Gamma0_prec <: Precedence.

Definition A : Set := Gamma0_sig.symb.
Import Gamma0_sig.

Definition prec : relation A :=
   fun f g => match f, g with
                      | nat_0, nat_S => True
                      | nat_0, ord_zero => True
                      | nat_0, ord_cons => True
                      | nat_0, ord_psi  => True
                      | ord_zero, nat_S => True
                      | ord_zero, ord_cons => True
                      | ord_zero, ord_psi => True
                      | nat_S, ord_cons => True
                      | nat_S, ord_psi => True
                      | ord_cons, ord_psi => True
                      | _, _ => False
                      end.


Inductive status_type : Set :=
  | Lex : status_type
  | Mul : status_type.

Definition status : A -> status_type := fun f => Lex.

Lemma prec_dec : forall a1 a2 : A, {prec a1 a2} + {~ prec a1 a2}.
Proof.
intros a1 a2; destruct a1; destruct a2;
  ((right; intro; contradiction)||(left;simpl;trivial)).
Qed.

Lemma prec_antisym : forall s, prec s s -> False.
Proof.
intros s; destruct s; simpl; trivial.
Qed.

Lemma prec_transitive : transitive A prec.
Proof.
intros s1 s2 s3; destruct s1; destruct s2; destruct s3; simpl; intros; trivial; contradiction.
Qed.

End Gamma0_prec.

Module Gamma0_alg <: Term := term.Make (Gamma0_sig) (Vars).
Module Gamma0_rpo <: RPO := rpo.Make (Gamma0_alg) (Gamma0_prec).

Import Gamma0_alg.
Import Gamma0_rpo.
Import Gamma0_sig.

(* coucou *)

Fixpoint nat_2_term (n:nat) : term :=
  match n with 0 => (Term nat_0 nil)
             | S p => Term nat_S ((nat_2_term p)::nil)
  end.



(** * Every (representation of a) natural number is less than
 a non zero ordinal *)

Lemma nat_lt_cons : forall (n:nat) t p  c , rpo (nat_2_term n) 
                                     (Term ord_cons (t::p::c::nil)).
 induction n;simpl.
 constructor 2.
 simpl; trivial.
 destruct 1.
 constructor 2.
 simpl; trivial.
 inversion_clear 1.
 subst s';apply IHn.
 case H0.
Qed.


Lemma nat_lt_psi : forall (n:nat) a b  , rpo (nat_2_term n) 
                                     (Term ord_psi (a::b::nil)).
 induction n;simpl.
 constructor 2.
 simpl; trivial.
 destruct 1.
 constructor 2.
 simpl; trivial.
 inversion_clear 1.
 subst s';apply IHn.
 case H0.
Qed.



Theorem rpo_trans : forall t t1 t2, rpo t t1 -> rpo t1 t2 -> rpo t t2.
 intros.
 case (rpo_closure t2 t1 t);eauto with T2.
Qed.


Fixpoint T2_2_term (a:T2) : term := 
match a with
 zero => Term ord_zero nil
|cons a b 0 zero => Term ord_psi (T2_2_term a :: T2_2_term b ::nil)
|cons a b n c => Term ord_cons (Term ord_psi (T2_2_term a :: T2_2_term b ::nil) ::nat_2_term n ::
                                T2_2_term c::nil)
end.

Fixpoint T2_size (o:T2):nat :=
 match o with zero => 0
            | cons a b n c => S (T2_size a + T2_size b + n + T2_size c)%nat
         end.


Lemma T2_size1 : forall a b n c, (T2_size zero < T2_size (cons a b n c))%nat.
Proof.
 simpl;auto with T2 arith.
Qed.


Lemma T2_size2 : forall a b n c , (T2_size a < T2_size (cons a b n c))%nat.
Proof.
 simpl; auto with arith T2.
Qed.


Lemma T2_size3 : forall a b n c , (T2_size b < T2_size (cons a b n c))%nat.
Proof.
 simpl; auto with arith T2.
Qed.

Lemma T2_size4 : forall a b n c , (T2_size c < T2_size (cons a b n c))%nat.
Proof.
 simpl; auto with arith T2.
Qed.



Hint Resolve T2_size1 T2_size2 T2_size3 T2_size4.


(** let us recall subterm properties on T2 *)


Lemma lt_subterm1 : forall a a'  n'  b' c', a < a' ->
                                         a < cons a'  b' n' c'.
Proof.
 intros.
 apply transitivity with (cons a b' n' c');auto with T2 .
Qed.

Hint Resolve nat_lt_cons.
Hint Resolve  lt_subterm1. 


Lemma nat_2_term_mono : forall n n', (n < n')%nat -> 
                                      rpo (nat_2_term n) (nat_2_term n').
Proof.
 induction 1.
 simpl.
 eapply Subterm.
 eleft.
 esplit.
 constructor.
 simpl.
 eapply Subterm.
 eleft.
 esplit.
 constructor.
 auto with T2.
Qed.


Lemma T2_size_psi : forall a b n c , 
    (T2_size [a,b] <= T2_size (cons a b n c))%nat.
Proof.
 simpl; auto with arith T2.
 intros;omega.
Qed.


(* Lemmas for rpo *)
Lemma rpo_2_2 : forall ta1 ta2 tb1 tb2 ,
                rpo ta1 ta2 ->
                rpo tb1 (Term ord_psi (ta2:: tb2::nil)) ->
                 rpo (Term ord_psi (ta1:: tb1 ::nil))
                     (Term ord_psi (ta2:: tb2 ::nil)).
Proof.
 intros.
 apply Top_eq_lex.
 simpl;auto with T2.
 left.
 auto with T2.
 auto with T2.
 inversion_clear 1; try subst s'.
 apply rpo_trans with ta2;auto with T2.
 eapply Subterm.
 2:eleft.
 left.
 auto with T2.
 decompose [or] H2.
 subst s'.
 auto with T2.
 case H1.
Qed.


Lemma rpo_2_3 : forall ta1 ta2 tb1 tb2 n1 tc1,
                rpo ta1 ta2 ->
                rpo tb1 (Term ord_psi (ta2:: tb2::nil)) ->
                rpo tc1 (Term ord_psi (ta1:: tb1::nil)) ->
                rpo (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::(nat_2_term n1) ::tc1::nil))
                    (Term ord_psi (ta2:: tb2 ::nil)).
Proof.
 intros.
 apply Top_gt.
 simpl;auto with T2.
 inversion_clear 1.
 subst s'.
 apply rpo_2_2;auto with T2.
 decompose [or] H3; try subst s'.
 apply nat_lt_psi.
 apply rpo_trans with (Term ord_psi (ta1 :: tb1 :: nil));auto with T2.
 apply rpo_2_2;auto with T2.
 case H4.
Qed.

Lemma rpo_2_1 : forall ta1 ta2 tb1 tb2 n1 n2 tc1 tc2,
                rpo ta1 ta2 ->
                rpo tb1 (Term ord_psi (ta2:: tb2::nil)) ->
                rpo tc1 (Term ord_psi (ta1:: tb1::nil)) ->
                rpo (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::(nat_2_term n1) ::tc1::nil))
                    (Term ord_cons ((Term ord_psi (ta2:: tb2 ::nil))::(nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply rpo_trans with (Term ord_psi (ta2 :: tb2 :: nil)).
 apply rpo_2_3;auto with T2.
 eapply Subterm.
 2:eleft.
 left;auto with T2.
Qed.






Lemma rpo_2_4 : forall ta1 ta2 tb1 tb2  n2  tc2,
                rpo ta1 ta2 ->
                rpo tb1 (Term ord_psi (ta2:: tb2::nil)) ->
                rpo (Term ord_psi (ta1:: tb1 ::nil))
                    (Term ord_cons ((Term ord_psi (ta2:: tb2 ::nil))::(nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply rpo_trans with (Term ord_psi (ta2 :: tb2 :: nil)). 
 apply rpo_2_2;auto with T2.
 eapply Subterm.
 eleft.
 reflexivity.
 left.
Qed.


Lemma rpo_3_2 : forall ta1  tb1 tb2 ,
                rpo tb1 tb2 ->
                rpo (Term ord_psi (ta1:: tb1 ::nil))
                    (Term ord_psi (ta1:: tb2 ::nil)).
Proof.
 intros.
 apply Top_eq_lex.
 simpl;auto with T2.
right.
 left.
 auto with T2.
 auto with T2.
 inversion_clear 1; try subst s'.
 eapply Subterm.
 eleft.
 reflexivity.
 left.
 decompose [or] H1;try subst s'.
 eapply rpo_trans with tb2;auto with T2.
 
 eapply Subterm.
 2:eleft.
 right;
 left.
 auto with T2.
 case H0.
Qed.


Lemma rpo_3_3 : forall ta1  tb1 tb2 n1 tc1,
                rpo tb1 tb2 ->
                rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
                rpo (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::(nat_2_term n1) ::tc1::nil))
                    (Term ord_psi (ta1:: tb2 ::nil)).
Proof.
 intros.
 apply Top_gt.
 simpl;auto with T2.
 inversion_clear 1; try subst s'.
 apply rpo_3_2;auto with T2.
 decompose [or] H2;try subst s'.
 apply nat_lt_psi.
 apply rpo_trans with (Term ord_psi (ta1 :: tb1 :: nil)).
auto with T2.
  apply rpo_3_2;auto with T2.
 case H3.
Qed.


Lemma rpo_3_1 : forall ta1  tb1 tb2 n1 n2 tc1 tc2,
                rpo tb1 tb2 ->
                rpo tc1 (Term ord_psi (ta1:: tb1::nil)) ->
                rpo (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::(nat_2_term n1) ::tc1::nil))
                    (Term ord_cons ((Term ord_psi (ta1:: tb2 ::nil))::(nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply rpo_trans with  (Term ord_psi (ta1 :: tb2 :: nil)).
 apply rpo_3_3;auto with T2.
 eapply Subterm.
 eleft.
 reflexivity.
 left;auto with T2.
Qed.


Lemma rpo_3_4 : forall ta1  tb1 tb2  n2  tc2,
                rpo tb1 tb2 ->
                rpo (Term ord_psi (ta1:: tb1 ::nil))
                    (Term ord_cons 
                      ((Term ord_psi (ta1:: tb2 ::nil))::
                                     (nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply rpo_trans with  (Term ord_psi (ta1 :: tb2 :: nil)).
 apply rpo_3_2;auto with T2.
 eapply Subterm.
 eleft.
 reflexivity.
 left;auto with T2.
Qed.


Lemma rpo_4_2 : forall ta1 ta2  tb1 tb2 ,
                rpo (Term ord_psi (ta1:: tb1 ::nil)) tb2 ->
                rpo (Term ord_psi (ta1:: tb1 ::nil))
                    (Term ord_psi (ta2:: tb2 ::nil)).
Proof.
 intros.
 apply rpo_trans with tb2;auto with T2.
 eapply Subterm.
 eright;eleft.
 reflexivity.
 left.
Qed.


Lemma rpo_4_3 : forall ta1  ta2 tb1 tb2 n1 tc1,
                rpo (Term ord_psi (ta1:: tb1 ::nil)) tb2 ->
                rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
                rpo (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::
                                                  (nat_2_term n1) ::tc1::nil))
                    (Term ord_psi (ta2:: tb2 ::nil)).
Proof.
 intros.
 apply Top_gt.
 simpl;auto with T2.
 inversion_clear 1; try subst s'.
 apply rpo_4_2;auto with T2.
 decompose [or] H2;try subst s'.
 apply nat_lt_psi.
 apply rpo_trans with (Term ord_psi (ta1 :: tb1 :: nil)).
 auto with T2.
 apply rpo_4_2;auto with T2.
 case H3.
Qed.




Lemma rpo_4_1 : forall ta1  ta2 tb1 tb2 n1 n2 tc1 tc2,
                rpo (Term ord_psi (ta1:: tb1 ::nil)) tb2 ->
                rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
                rpo 
                 (Term ord_cons 
                    ((Term ord_psi (ta1:: tb1 ::nil))::
                                   (nat_2_term n1) ::tc1::nil))
                     (Term ord_cons 
                              ((Term ord_psi (ta2:: tb2 ::nil))::
                                             (nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply rpo_trans with  (Term ord_psi (ta2 :: tb2 :: nil)).
 apply rpo_4_3;auto with T2.
 eapply Subterm.
 eleft.
 reflexivity.
 left;auto with T2.
Qed.




Lemma rpo_4_4 : forall ta1  ta2 tb1 tb2  n2  tc2,
                rpo (Term ord_psi (ta1:: tb1 ::nil)) tb2 ->
                rpo (Term ord_psi (ta1:: tb1 ::nil))
                    (Term ord_cons 
                     ((Term ord_psi (ta2:: tb2 ::nil))::
                      (nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply rpo_trans with  (Term ord_psi (ta2 :: tb2 :: nil)).
 apply rpo_4_2;auto with T2.
 eapply Subterm.
 eleft.
 reflexivity.
 left;auto with T2.
Qed.


Lemma rpo_5_2 : 
           forall ta1 ta2  tb1  ,
              rpo (Term ord_psi (ta1:: tb1 ::nil))
                 (Term ord_psi (ta2:: (Term ord_psi (ta1::tb1::nil)) ::nil)).
Proof.
 intros.
 eapply Subterm.
 eright;eleft.
 reflexivity.
 left.
Qed.


Lemma rpo_5_3 : forall ta1  ta2 tb1  n1 tc1,
                rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
                rpo 
                (Term ord_cons 
                 ((Term ord_psi (ta1:: tb1 ::nil))::
                                (nat_2_term n1) ::tc1::nil))
                (Term ord_psi (ta2:: (Term ord_psi (ta1:: tb1 ::nil)) ::nil)).
Proof.
 intros.
 apply Top_gt.
 simpl;auto with T2.
 inversion_clear 1; try subst s'.
 apply rpo_5_2;auto with T2.
 decompose [or] H1;try subst s'.
 apply nat_lt_psi.
 apply rpo_trans with (Term ord_psi (ta1 :: tb1 :: nil)).
 auto with T2.
 apply rpo_5_2;auto with T2.
 case H2.
Qed.




Lemma rpo_5_1 : forall ta1  ta2 tb1  n1 n2 tc1 tc2,
                rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
                rpo 
                (Term ord_cons 
                 ((Term ord_psi (ta1:: tb1 ::nil))::
                                (nat_2_term n1) ::tc1::nil))
                    (Term ord_cons
                       ((Term ord_psi (ta2:: 
                                      (Term ord_psi (ta1:: tb1 ::nil))
                                       ::nil))::
                       (nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply rpo_trans with  
    (Term ord_psi (ta2 :: Term ord_psi (ta1 :: tb1 :: nil) :: nil)).
 apply rpo_5_3.
 auto with T2.
 eapply Subterm.
 eleft.
 reflexivity.
 left;auto with T2.
Qed.


Lemma rpo_5_4 : forall ta1  ta2 tb1  n2  tc2,
                rpo (Term ord_psi (ta1:: tb1 ::nil))
                    (Term ord_cons
                       ((Term ord_psi (ta2:: 
                                      (Term ord_psi (ta1:: tb1 ::nil))
                                       ::nil))::
                       (nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply rpo_trans with 
     (Term ord_psi (ta2 :: Term ord_psi (ta1 :: tb1 :: nil) :: nil)).
 
 eapply Subterm.
 eright;eleft.
 reflexivity.
 left.
 eapply Subterm.
 eleft.
 reflexivity.
 left.
Qed.



Lemma rpo_6_1 : forall ta1 tb1 n1 n2 tc1 tc2,
 rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
 (n1 < n2)%nat ->
   rpo 
    (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::
                                  (nat_2_term n1) ::tc1::nil))
    (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::
                                  (nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 apply Top_eq_lex.
 simpl;auto with T2.
 right.
 left.
 apply nat_2_term_mono;auto with T2.
 auto with T2.
 inversion_clear 1; try subst s'.
 eapply Subterm.
 2:eleft.
 left;auto with T2.
 decompose [or] H2;try subst s'.
 apply nat_lt_cons.
 eapply rpo_trans.
 eexact H.
 eapply Subterm.
 2:eleft.
 left;auto with T2.
 case H3.
Qed.



Lemma rpo_6_4 : forall ta1 tb1  n2  tc2,
 (0 < n2)%nat ->
   rpo (Term ord_psi (ta1:: tb1 ::nil))
       (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::
                                     (nat_2_term n2) ::tc2::nil)).
Proof.
 intros.
 eapply Subterm.
 2:eleft.
 left;auto with T2.
Qed.




Lemma rpo_7_1 : forall ta1 tb1 n1 tc1 tc2,
 rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
 rpo tc1  tc2 ->
 rpo (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::
                                   (nat_2_term n1) ::tc1::nil))
                    (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))::
                                    (nat_2_term n1) ::tc2::nil)).
Proof.
 intros.
 apply Top_eq_lex.
 simpl;auto with T2.
 right.
 right.
 left.
 auto with T2.
 auto with T2.
 inversion_clear 1; try subst s'.
 eapply Subterm.
 2:eleft.
 left;auto with T2.
 decompose [or] H2;try subst s'.
 apply nat_lt_cons.
 eapply rpo_trans.
 eexact H.
 eapply Subterm.
 2:eleft.
 left;auto with T2. 
 case H3.
Qed.


Section lt_incl_rpo.
 Variable s :nat.
 Variables (a1 b1 c1 a2 b2 c2:T2)(n1 n2:nat).

 Hypothesis Hsize :
   ((T2_size (cons a1 b1 n1 c1) + T2_size (cons a2 b2 n2 c2)) = S s)%nat.

 Hypothesis Hrec :   forall o' o, (T2_size o + T2_size o' <= s)%nat->
                              o < o' -> nf o -> nf o' -> 
                                  rpo (T2_2_term o) (T2_2_term o').

 Hypothesis nf1 : nf (cons a1 b1 n1 c1).
 Hypothesis nf2 :  nf (cons a2 b2 n2 c2).

 Remark nf_a1 : nf a1.
 Proof.
  nf_inv.
 Qed.

 Remark nf_a2 : nf a2.
 Proof.
  nf_inv.
 Qed.

 Remark nf_b1 : nf b1.
 Proof.
  nf_inv.
 Qed.

 Remark nf_b2 : nf b2.
 Proof.
  nf_inv.
 Qed.
 Hint Resolve nf1 nf2 nf_a1 nf_a2 nf_b1 nf_b2.

  Remark nf_c1 : nf c1.
 Proof.
  nf_inv.
 Qed.

 Remark nf_c2 : nf c2.
 Proof.
  nf_inv.
 Qed.

 Hint Resolve nf_c1 nf_c2.

Hypothesis H : cons a1 b1 n1 c1 < cons a2 b2 n2 c2.


Lemma cons_rw : forall a b n c, 
 (n=0 /\ c=zero /\ 
   (T2_2_term (cons a b n c)=(Term ord_psi 
         ((T2_2_term a)::(T2_2_term b)::nil)))) \/
    (T2_2_term (cons a b n c)=
                        Term ord_cons 
                          ((Term ord_psi ((T2_2_term a)::(T2_2_term b)::nil))
                                        ::(nat_2_term n)::(T2_2_term c)::nil)).
 

 destruct n. 
 destruct c.
 left;simpl;auto with T2.
 right;simpl;auto with T2.
 right;simpl;auto with T2.
Qed.


 
Lemma lt_rpo_cons_cons : rpo (T2_2_term (cons a1 b1 n1 c1)) 
                     (T2_2_term (cons a2 b2 n2 c2)).
Proof.
 inversion H.
 assert (rpo (T2_2_term a1) (T2_2_term a2)).
 apply Hrec.
 simpl in Hsize;omega.
 auto with T2.
 auto with T2.
 auto with T2.
 assert (rpo (T2_2_term b1) 
             (Term ord_psi ((T2_2_term a2):: ((T2_2_term b2)::nil)))).
 change (rpo (T2_2_term b1) (T2_2_term (cons a2 b2 0 zero))).
 apply Hrec.
 simpl;simpl in Hsize;omega.
 auto with T2.
 auto with T2.
 constructor;auto with T2.
 assert (rpo (T2_2_term c1) (Term ord_psi (T2_2_term a1 :: T2_2_term b1 :: nil))).
  change (rpo (T2_2_term c1) (T2_2_term (cons a1 b1 0 zero))).
  apply Hrec.
 simpl;simpl in Hsize;omega.
  inversion_clear nf1.
 auto with T2.
 apply psi_relevance;auto with T2.
 auto with T2.
 constructor;auto with T2.
 case (cons_rw a1 b1 n1 c1).
 intros (H'2,(H'3,H'4)).
 rewrite H'2;rewrite H'3.
  case (cons_rw a2 b2 n2 c2).
  intros (H'5,(H'6,H'7)).
 rewrite H'5;rewrite H'6.
 simpl.
 apply rpo_2_2;auto with T2.
 intro H'6;rewrite H'6.
 simpl.
 apply rpo_2_4 ; auto with T2.
 intro H'6;rewrite H'6.
 case (cons_rw a2 b2 n2 c2).
 intros (H''5,(H''6,H''7)).
 rewrite H''7. 
 apply rpo_2_3;auto with T2.
 intro H'7;rewrite H'7.
 apply rpo_2_1;auto with T2.
 subst a2.
 assert (rpo (T2_2_term b1) (T2_2_term b2)).
 apply Hrec.
 simpl in Hsize;omega.
 auto with T2.
 auto with T2.
 auto with T2.
 assert (rpo (T2_2_term c1) 
             (Term ord_psi (T2_2_term a1 :: T2_2_term b1 :: nil))).
 change (rpo (T2_2_term c1) (T2_2_term (cons a1 b1 0 zero))).
 apply Hrec.
 simpl;simpl in Hsize;omega.
 inversion_clear nf1.
 auto with T2.
 apply psi_relevance;auto with T2.
 auto with T2.
 constructor;auto with T2.
 case (cons_rw a1 b1 n1 c1).
 intros (H'2,(H'3,H'4)).
 rewrite H'4.
 case (cons_rw a1 b2 n2 c2).
 intros (H'5,(H'6,H'7)).
 rewrite H'7.
 apply rpo_3_2;auto with T2.
 intro H'6;rewrite H'6.
 apply rpo_3_4 ; auto with T2.
 intro H'6;rewrite H'6.
 case (cons_rw a1 b2 n2 c2).
 intros (H''5,(H''6,H''7)).
 rewrite H''7.
 apply rpo_3_3;auto with T2.
 intro H'7;rewrite H'7.
 apply rpo_3_1;auto with T2.
 assert  (rpo (Term ord_psi ((T2_2_term a1):: (T2_2_term b1) ::nil))
              (T2_2_term b2)).
 change  (rpo (T2_2_term (cons a1 b1 0 zero))  (T2_2_term b2)).
 apply Hrec.
 simpl in Hsize. 
 simpl;omega.
 auto with T2.
 auto with T2.
 auto with T2.
  assert (rpo (T2_2_term c1) 
              (Term ord_psi (T2_2_term a1 :: T2_2_term b1 :: nil))).
  change (rpo (T2_2_term c1) (T2_2_term (cons a1 b1 0 zero))).
  apply Hrec.
 simpl;simpl in Hsize;omega.
  inversion_clear nf1.
 auto with T2.
 apply psi_relevance;auto with T2.
 auto with T2.
 constructor;auto with T2.

 case (cons_rw a1 b1 n1 c1).
 intros (H'2,(H'3,H'4)).
 rewrite H'4.
 
  case (cons_rw a2 b2 n2 c2).
  intros (H'5,(H'6,H'7)).
  rewrite H'7.
 apply rpo_4_2;auto with T2.
 intro H'6;rewrite H'6.
 apply rpo_4_4 ; auto with T2.
 intro H'6;rewrite H'6.
 case (cons_rw a2 b2 n2 c2).
 intros (H''5,(H''6,H''7)).
 rewrite H''7.
 apply rpo_4_3;auto with T2.
 intro H'7;rewrite H'7.
 apply rpo_4_1;auto with T2.
 assert (rpo (T2_2_term c1) 
             (Term ord_psi ((T2_2_term a1)::(T2_2_term b1)::nil))).
 change (rpo (T2_2_term c1) (T2_2_term (cons a1 b1 0 zero))).
  apply Hrec.
 simpl;simpl in Hsize;omega.
 inversion_clear nf1;auto with T2.
 apply psi_relevance;auto with T2.
 auto with T2.
 constructor;auto with T2.
 case (cons_rw a1 b1 n1 c1).
 intros (H'2,(H'3,H'4)).
 rewrite H'4.
 case (cons_rw a2 (cons a1 b1 0 zero) n2 c2).
  intros (H''5,(H''6,H''7)).
  rewrite H''7.
 simpl;apply rpo_5_2;auto with T2.
 intro H'7;rewrite H'7.
 simpl;apply rpo_5_4.
 intro H'7;rewrite H'7.
 case (cons_rw a2 (cons a1 b1 0 zero) n2 c2).
 intros (H''5,(H''6,H''7)).
  rewrite H''7.
  simpl;apply rpo_5_3.
  auto with T2.
 intro H''7;rewrite H''7.
  simpl;apply rpo_5_1.
 auto with T2.
 subst a2.
 subst b2.
 assert (rpo (T2_2_term c1) 
             (Term ord_psi ((T2_2_term a1):: (T2_2_term b1) ::nil))).  
 change (rpo (T2_2_term c1) (T2_2_term (cons a1 b1 0 zero))).
 apply Hrec.
 simpl; simpl in Hsize;omega.
 inversion nf1;auto with T2.
 apply psi_relevance;auto with T2.
 auto with T2.
 constructor;auto with T2.
  case (cons_rw a1 b1 n1 c1).
 intros (H'2,(H'3,H'4)).
 rewrite H'4.
  case (cons_rw a1 b1 n2 c2).
 intros (H''2,(H''3,H''4)).
 rewrite H''2 in H1.
 inversion H1.
 intro H'7;rewrite H'7.
 apply rpo_6_4.
 rewrite H'2 in H1;auto with T2.
 intro H'7;rewrite H'7.
  case (cons_rw a1 b1 n2 c2).
  intros (H''2,(H''3,H''4)).
 rewrite H''2 in H1.
inversion H1.
 intro H''7;rewrite H''7.
 apply rpo_6_1.
 auto with T2.
 auto with T2.
 assert (rpo (T2_2_term c1)
             (Term ord_psi ((T2_2_term a1):: (T2_2_term b1) ::nil))).  
 change (rpo (T2_2_term c1) (T2_2_term (cons a1 b1 0 zero))).
 apply Hrec.
 simpl; simpl in Hsize;omega.
 inversion nf1;auto with T2.
 apply psi_relevance;auto with T2.
 auto with T2.
 constructor;auto with T2.
 assert (rpo (T2_2_term c1) (T2_2_term c2)).
 apply Hrec.
 simpl; simpl in Hsize;omega.
 auto with T2.
 auto with T2.
 auto with T2.
 case (cons_rw a2 b2 n2 c1).
 intros (H'2,(H'3,H'4)).
 rewrite H'4.
  case (cons_rw a2 b2 n2 c2).
 intros (H''2,(H''3,H''4)).
 rewrite H''3 in H1.
 inversion H1.
 intro H'7;rewrite H'7.
 eapply Subterm.
 2:eleft.
 left.
 auto with T2.
 intro H'7;rewrite H'7.
 case (cons_rw a2 b2 n2 c2).
 intros (H''2,(H''3,H''4)).
 rewrite H''3 in H1;inversion H1.
 intro H''7;rewrite H''7.
 apply rpo_7_1.
 auto with T2.
 subst a2;subst b2.
 auto with T2.
 auto with T2.
Qed.


End lt_incl_rpo.

Lemma lt_inc_rpo_0 : forall n, 
                           forall o' o, (T2_size o + T2_size o' <= n)%nat->
                              o < o' -> nf o -> nf o' -> 
                                  rpo (T2_2_term o) (T2_2_term o').
Proof.
induction n.
destruct o;destruct o'.
inversion 2.
simpl.
inversion 1.
inversion 2.
simpl.
inversion 1.
destruct o'.
inversion 2.
destruct o.
intros. 
case (cons_rw o'1 o'2 n0 o'3).
intros (H'1,(H'2,H'3)).
rewrite H'3.
simpl;apply Top_gt.
simpl;auto with T2.
destruct 1.
intro H3;rewrite H3.
simpl;apply Top_gt.
simpl;auto with T2.
destruct 1.
intros. 
case (le_lt_or_eq _ _ H).
 intros;apply IHn;auto with arith T2.

 intros;
eapply lt_rpo_cons_cons;eauto with T2.
Qed.



Remark R1 : Acc P.prec nat_0. 
 split.
 destruct y; try contradiction.
Qed.

Hint Resolve R1.

Remark R2 : Acc P.prec ord_zero. 
 split.
 destruct y; try contradiction; auto with T2.
Qed.

Hint Resolve R2.

Remark R3 : Acc P.prec nat_S.
 split.
 destruct y; try contradiction;auto with T2.
Qed.


Hint Resolve R3.

Remark R4 : Acc P.prec ord_cons.
 split.
 destruct y; try contradiction;auto with T2.
Qed.

Hint Resolve R4.

Remark R5 : Acc P.prec ord_psi.
 split.
 destruct y; try contradiction;auto with T2.
Qed.

Hint Resolve R5.

Theorem well_founded_rpo : well_founded rpo.
Proof.
 apply wf_rpo.
 red.
 destruct a;auto with T2.
Qed.

Section  well_founded.
 
  Let R := restrict T2 nf lt.

  Hint Unfold restrict R.

 Lemma R_inc_rpo : forall o o', R o o' -> rpo (T2_2_term o) (T2_2_term o').
 Proof.
  intros o o' (H,(H1,H2)).
  eapply lt_inc_rpo_0;auto with T2.
 Qed. 

 
 Lemma nf_Wf : well_founded_P _ nf lt.
Proof.
 unfold well_founded_P.
 intros.
 unfold restrict.
 generalize (Acc_inverse_image _ _ rpo T2_2_term a (well_founded_rpo (T2_2_term a))).
  intro.
 eapply  Acc_incl  with  (fun x y : T2 => rpo (T2_2_term x) (T2_2_term y)). 
 red.
 apply R_inc_rpo.
 auto with T2.
Qed.


End well_founded.






Definition transfinite_induction :
 forall (P:T2 -> Type),
   (forall x:T2, nf x ->
                   (forall y:T2, nf y ->  y < x -> P y) -> P x) ->
    forall a, nf a -> P a.
Proof.
 intros; eapply P_well_founded_induction_type; eauto with T2.
 eexact nf_Wf;auto with T2.
Defined.


Definition transfinite_induction_Q :
  forall (P : T2 -> Type) (Q : T2 -> Prop),
      (forall x:T2, Q x -> nf x ->
           (forall y:T2, Q y -> nf y ->  y < x -> P y) -> P x) ->
   forall a, nf a -> Q a -> P a.
Proof.
 intros.
 eapply P_well_founded_induction_type with (R:=lt)(P:=fun a => nf a /\ Q a).
 3:split;auto with T2.
 2:destruct 1; intros; eapply X; eauto with T2.
 unfold well_founded_P.
 intros.
 apply Acc_incl with (restrict _ nf lt).
 unfold inclusion; intros.
 unfold restrict.
 unfold restrict in H2.
 tauto.
 apply nf_Wf.
 case H1;auto with T2.
Defined.




(* the Veblen function phi *)

Definition  phi (alpha beta : T2) : T2 :=
 match beta with zero => [alpha, beta] 
               | [b1, b2] => 
                 (match compare alpha b1
                   with Datatypes.Lt => [b1, b2 ]
                       | _ => [alpha,[b1, b2]]
                                           end)
               | cons b1 b2 0 (cons zero zero  n zero) => 
                       (match compare alpha b1
                        with  Datatypes.Lt => 
                            [alpha, (cons b1 b2 0 (finite n))]
                            | _ =>  [alpha, (cons b1 b2 0 (finite (S n)))]
                        end)
              | any_beta => [alpha, any_beta]
end.



Theorem phi_of_psi  : forall a b1 b2, 
                      phi a [b1, b2] =
                      if (lt_ge_dec a b1) 
                      then [b1, b2]
                      else [a ,[b1, b2]].
 simpl.
 intros;case (lt_ge_dec a b1).
 intro;  rewrite compare_rw_lt; auto with T2.
 destruct 1.
 subst b1; rewrite compare_rw_eq;auto with T2.
 rewrite compare_rw_gt;auto with T2.
Qed.

Lemma phi_to_psi : forall alpha beta, 
      {alpha' : T2 & {beta' : T2 | phi alpha beta = [alpha', beta']}}.
Proof.
 destruct beta;simpl.
 exists alpha; exists zero;trivial.
 case n.
 
 case beta3. 
 case (compare alpha beta1). 
 
 exists alpha;exists  [beta1, beta2];trivial.
 exists beta1;exists beta2;trivial.
 
 exists alpha;exists  [beta1, beta2];trivial.

 
 destruct t.
 destruct t.
 destruct n0.
 destruct t.
 case (compare alpha beta1).
 exists alpha;exists (cons beta1 beta2 0 [zero, zero]);trivial.
 exists alpha;exists (cons beta1 beta2 0 zero);trivial.
 exists alpha;exists (cons beta1 beta2 0 [zero, zero]);trivial.
 exists alpha;
   exists (cons beta1 beta2 0 (cons zero zero 0 (cons t1 t2 n0 t3)));
   trivial.
 destruct t.
 case (compare alpha beta1).
 exists alpha; exists (cons beta1 beta2 0 (cons zero zero (S n0) zero)).
 trivial.
 exists alpha;exists (cons beta1 beta2 0 (F S n0));trivial.
 exists alpha;exists ( cons beta1 beta2 0 (cons zero zero (S n0) zero));trivial.
 exists alpha;
  exists ( cons beta1 beta2 0 (cons zero zero (S n0) (cons t1 t2 n1 t3)));
 trivial.
 intros n1 t;exists alpha;
  exists (cons beta1 beta2 0 (cons zero (cons t1 t2 n0 t3) n1 t));trivial.
 exists alpha;exists (cons beta1 beta2 0 (cons (cons t1 t2 n0 t3) t n1 t0));
 trivial.
 intro n0;exists alpha;exists (cons beta1 beta2 (S n0) beta3);trivial.
Qed.

Lemma phi_principal : forall alpha beta, ap (phi alpha beta).
Proof.
 intros alpha beta; case (phi_to_psi alpha beta);intros x (y,E);
  rewrite E;try constructor.
Qed.



Theorem phi_alpha_zero : forall alpha, phi alpha zero = [alpha, zero].
Proof.
 simpl;auto with T2.
Qed.




Theorem phi_of_psi_succ : forall a b1 b2 n, (* nf b1 -> nf b2 -> *)
                          phi a (cons b1 b2 0 (finite (S n))) =
                          if lt_ge_dec a b1
                          then [a, (cons b1 b2 0 (finite n))]
                          else [a ,(cons b1 b2 0 (finite (S n)))].

 simpl.
 intros;case (lt_ge_dec a b1).
 intro;  rewrite compare_rw_lt; auto with T2.
 destruct 1.
 subst b1; rewrite compare_rw_eq;auto with T2.
 rewrite compare_rw_gt;auto with T2.
Qed.

(*
Theorem phi_of_psi_gen : forall a b1 b2 n b3,
   b1 <= a ->
   phi a (cons b1 b2 n b3) = psi a (cons b1 b2 n b3).
*)


(* every principal ordinal is enumerated by phi zero *)







Lemma phi_cases_aux : forall P : T2 -> Type,
                         P zero ->
                         (forall b1 b2, nf b1 -> nf b2 -> P [b1, b2]) ->
                         (forall b1 b2 n, nf b1 -> nf b2 ->
                                       P (cons b1 b2 0 (finite (S n)))) ->
                         (forall b1 b2 n c, nf (cons b1 b2 n c) ->
                                   omega <= c \/ (0 < n)%nat -> 
                                   P (cons b1 b2 n c)) ->
                         forall alpha, nf alpha -> P alpha.
 intros until alpha.
 case alpha.
 auto with T2.
 destruct n;intros until t1;case (lt_ge_dec t1 omega).
intros.
 assert (nf t1).
 inversion H;auto with T2.
 
 case (lt_omega_inv  H0 l).
 intro x;case x.
 intro;subst t1.
 simpl.
 refine (X0 _ _ _ _).
 inversion H;auto with T2.
 inversion H;auto with T2.
 intros;subst t1.
 apply X1.
 inversion H;auto with T2.
 inversion H;auto with T2.
 intros;apply X2.
 auto with T2.
 auto with T2.
 intros;apply X2.
 auto with T2.
 auto with arith T2.
 intros;apply X2.
 auto with T2.
 auto with T2.
Qed.

 
Theorem phi_cases' : forall a b, nf b ->
                    {b1 :T2 & {b2:T2 | b = [b1, b2] /\
                                       a < b1 /\ phi a b =  b}} +
                    {phi a b = [a, b]} +
                     {b1 :T2 & {b2:T2 & {n: nat |
                              b = cons b1 b2 0 (finite (S n))/\
                              a < b1 /\ 
                              phi a b = [a, (cons b1 b2 0 (finite n))]}}}.
 intros a b Hb.
 pattern b; apply phi_cases_aux.
 left;right;simpl;auto with T2.
 intros.
 caseEq (compare a b1).
 left;right.
 unfold phi.
 simpl.
 rewrite H1;auto with T2.
 left.
 left. 
 exists b1;exists b2; split.
 auto with T2.
 split;simpl;auto with T2. 
 rewrite H1;auto with T2.
 left;right.
 simpl.
 rewrite H1;auto with T2.
  intros.
 caseEq (compare a b1).
 left;right.
 simpl.
 rewrite H1.
 auto with T2.
 right.
 exists b1;exists b2; exists n.
 repeat split;auto with T2.
 simpl.
 rewrite H1;auto with T2.
 left;right.
 simpl.
 rewrite H1;auto with T2.
 intros.
 left;right.
 simpl.
 caseEq n.
 intro; subst n.
 caseEq c.
 intro; subst c.
 case H0.
 destruct 1.
 discriminate H1.
 inversion H1.
 inversion 1.
 intro t;case t.
 intro t0;case t0.
 intros until t1;case t1.
 intro; subst c.
 case H0.
 destruct 1.
 discriminate H1.
 inversion H1; lt_clean; auto with T2.
 inversion 1.
 auto with T2.
 auto with T2.
 auto with T2.
 auto with T2.
auto with T2.
Qed.

Theorem phi_cases : forall a b, nf b ->
                      {phi a b = b}+
                      {phi a b= [a, b]}+
                      {b': T2 | nf b' /\ phi a b = [a, b']
                                       /\ succ  b' = b}.
Proof.
 intros a b Hb. 
 pattern b;apply phi_cases_aux.
 left;right.
 simpl; auto with T2.
 intros.
 generalize (phi_of_psi a b1 b2).
 case (lt_ge_dec a b1).
 left;left;auto with T2.
 left;right;auto with T2.
 intros. 
 generalize (phi_of_psi_succ a  b1 b2 n).
 case (lt_ge_dec a b1).
 right.
 exists (cons b1 b2 0 (finite n)).
 split.
 case n.
 simpl;constructor;auto with T2.
 simpl.
 repeat constructor;auto with T2.
 apply le_lt_trans with a;auto with T2.
 (* apply le_zero_alpha.*)

 (* ICI *)
 split; auto with T2.
 simpl.
 generalize l;case b1.
 inversion 1.
 case n;simpl;auto with T2.
 left;right.
 auto with T2.
 left;right;simpl.
 caseEq n.
 intro;subst n.
 caseEq c.
 intro; subst c.
 case H0;intro.
 inversion H1.
 discriminate H2.
 lt_clean.
 lt_clean.
 intro t; case t.
 intro t0;case t0.
 intros n t1 e; subst c.
  case H0.
 unfold omega; destruct 1.
 discriminate H1.
 inversion H1; lt_clean;auto with T2.
 inversion 1.
 auto with T2.
 auto with T2.
 auto with T2.
 auto with T2.
Qed.
 



Theorem phi_nf : forall alpha beta, nf alpha -> 
                                     nf beta -> 
                                     nf (phi alpha beta).
 intros t1 t2 v1 v2; case (phi_cases t1 v2).
 destruct 1.
 rewrite e;auto with T2.
 rewrite e;unfold psi;constructor;auto with T2.
 destruct 1 as (b', (V,(H,H0))).
 rewrite H.
 unfold psi;constructor;auto with T2.
Qed.




Lemma phi_of_any_cons : forall alpha beta1 beta2 n gamma, 
(*                        nf (cons beta1 beta2 n gamma) -> *)
                        omega <= gamma  \/ (0 < n)%nat ->
                        phi alpha (cons beta1 beta2 n gamma) = 
                        [alpha, (cons beta1 beta2 n gamma)].
 simpl.
 intros until n; case n.
 destruct 1.
 generalize H; case gamma.
 destruct 1.
 discriminate H0.
 lt_clean.
 intro t;case t.
 intro t0;case t0.
 destruct 1.
 discriminate H0.
 inversion H0; lt_clean; auto with T2.
 auto with T2.
 auto with T2.
 lt_clean.
 auto with T2.
Qed.



Lemma phi_fix : forall alpha beta, phi alpha beta = beta ->
                      {beta1 : T2 & {beta2 : T2 | beta = [beta1, beta2] 
                                                  /\ alpha < beta1}}.
Proof.
 destruct beta;simpl.
 discriminate 1.
 case n.
 case beta3.
 caseEq (compare  alpha beta1).
 intros.
 injection H0.
 intro;
 absurd (lt beta2 [beta1, beta2]).
 rewrite H1; apply lt_irr.
 refine (lt_beta_psi _ _).
 exists beta1.
 exists beta2; split;auto with T2.
 intros.
 injection H0.
  intro;
 absurd (beta2 < [beta1, beta2]).
 rewrite H1;apply lt_irr.
 refine (lt_beta_psi _ _).
 destruct t;simpl.
 destruct t;simpl.
 destruct t;simpl.
 case (compare alpha beta1).
 discriminate 1.
 discriminate 1.
 discriminate 1.
 discriminate 1.
 discriminate 1.
 discriminate 1.
 discriminate 1.
 Qed.


Lemma phi_le : forall alpha beta alpha' beta', 
                  nf beta -> 
                  phi alpha beta = [alpha', beta'] -> alpha <= alpha'.
Proof.
 intros a b a' b' Hb;case (phi_cases a Hb).
 destruct 1.
 case (phi_fix _  e).
 intros x (beta2,(H,H0)).
 rewrite e.
 rewrite H.
 injection 1.
 intros; subst x; right;auto with T2.
 rewrite e;injection 1;left;auto with T2.
 intros (b0,(H1,(H2,H3))).
 rewrite H2; injection 1;left;auto with T2.
Qed.




 


Lemma phi_le_ge : forall alpha beta, nf alpha -> nf beta -> 
     {alpha':T2 &
        {beta':T2 | phi alpha beta = [alpha' ,beta'] /\  
                    alpha <= alpha' /\ 
                    beta' <= beta}}.
Proof.
 intros a b Va Vb; case (phi_cases' a Vb).
 destruct 1.
 case s; intros b1 (b2,(H1,(H2,H3))).
 rewrite H1 in H3.
 subst b.
 exists b1;exists  b2;repeat split;auto with T2.
 exists a;exists b;auto with T2.
 intros (b1,(b2,(n,(H1,(H2,H3))))).
 exists a;exists (cons b1 b2 0 (finite n));auto with T2.
split;auto with T2.
 split;auto with T2.
 subst b;case n;simpl; auto with T2.
 right;auto with T2.
Qed.

 
Theorem phi_spec1 : forall alpha beta gamma, 
                         nf alpha -> nf beta -> nf gamma ->
                         gamma < alpha ->
                        phi gamma (phi alpha beta) = phi alpha beta.
 intros.
 case (phi_le_ge H H0 ).
 intros alpha' (beta', (H'1,(H'2,H'3))).
 rewrite H'1.
 simpl.
 rewrite (compare_rw_lt);auto with T2.
 apply lt_le_trans with alpha;auto with T2.
Qed.


Theorem phi_principalR : forall alpha beta, nf alpha -> nf beta ->
                {gamma:T2 | [alpha, beta] =  phi zero gamma}.
 intros alpha beta Valpha Vbeta; case (phi_cases' alpha Vbeta).
 destruct 1.
 case s; intros b1 (b2,(H1,(H2,H3))).
 case (lt_ge_dec zero alpha).
 intro.
 exists [alpha, beta].
 simpl.
 rewrite (compare_rw_lt  l);auto with T2.
 intro; assert(alpha = zero).
 inversion l;auto with T2.
 lt_clean.
 subst alpha.
 subst beta.
 exists (cons b1 b2 0 (F 1)).
 simpl.
  rewrite (compare_rw_lt  H2);auto with T2.
 case (lt_ge_dec zero alpha). 
 exists (phi alpha beta).
 rewrite phi_spec1;auto with T2.
 intro;assert (alpha=zero).
 case l.
 auto with T2.
 intro;lt_clean.
 subst alpha.
 exists beta.
 auto with T2.
 intros (b1,(b2,(n,(H1,(H2,H3))))).
 subst beta.
 case (lt_ge_dec zero alpha).
 intro l.
 exists [alpha, (cons b1 b2 0 (F (S n)))].
 simpl.
 rewrite (compare_rw_lt l).
 auto with T2.
  intro;assert (alpha=zero).
 case l.
 auto with T2.
 intro;lt_clean.
 subst alpha.
 exists (cons b1 b2 0 (F (S (S n)))).
 simpl.
rewrite  (compare_rw_lt H2).
auto with T2.
Defined.

 


(* All epsilons are fixpoints of phi 0 *)

Theorem epsilon_fxp : forall beta, phi zero (epsilon beta) =
                                   epsilon beta.
 compute.
 trivial.
Qed.


 
Lemma no_critical : forall alpha, lt alpha (phi alpha zero).
 induction alpha;simpl;auto with T2.
Qed.


Theorem le_b_phi_ab : forall a b, nf a -> nf b ->  le b (phi a b).

 intros a b Ha Hb; case (phi_cases a  Hb).
 destruct 1.
 rewrite e;left;auto with T2.
 rewrite e;right; auto with T2.
 intro x; case x;intros b' (e,(i,i')).
 subst b.
  rewrite i.
 apply lt_succ_le;auto with T2.
Qed.

Lemma phi_of_psi_plus_finite : forall a b1 b2 n, 
                       a < b1 -> phi a (cons b1 b2 0 (finite n)) <
                                 [a ,(cons b1 b2 0 (finite n))].
simpl.
 intros until n;case n.
 simpl.
 intro H;rewrite (compare_rw_lt H);auto with T2.
 simpl.
  intros n0  H;rewrite (compare_rw_lt H).
 case n0;simpl; auto with T2.
Qed.
 

Lemma phi_mono_r : forall a b c, nf a -> nf b -> nf c ->
                     b < c -> phi a b < phi a c.
 intros a b c Ha Hb Hc H.
 case (phi_cases' a Hb).
 destruct 1.
 case s; intros b1 (b2,(H1,(H2,H3))).
 rewrite H3.
 apply lt_le_trans with c;auto with T2.
 apply le_b_phi_ab;auto with T2.
 case (phi_cases' a Hc).
 destruct 1.
 case s; intros c1 (c2,(H'1,(H'2,H'3))).
 rewrite e.
 rewrite H'3.
 rewrite H'1.
 constructor 2;auto with T2.
 rewrite H'1 in H.
 auto with T2.
 rewrite e;rewrite e0;auto with T2. 
 intros (c1,(c2,(n, (H1,(H2,H3))))).
 subst c.
 assert 
  ((cons c1 c2 0 (finite (S n))) = (succ (cons c1 c2 0 (finite n)))).
 simpl;auto with T2.
 caseEq c1.
 intro; subst c1; lt_clean.
 case n;auto with T2.
 assert (nf (cons c1 c2 0 (finite n))).
 case n.
 inversion Hc;auto with T2.
 inversion Hc;auto with T2.
 intro; simpl; constructor.
 constructor 2.
 apply le_lt_trans with a;auto with T2.
 auto with T2.
 inversion Hc;auto with T2.
 inversion Hc;auto with T2.
 repeat constructor.
 
 
 rewrite H0 in H.
 
case (succ_lt_le Hb H1 H).
 intro;subst b.
 case (lt_irr (alpha:=[a, (cons c1 c2 0 (finite n))])).
 pattern  [ a, (cons c1 c2 0 (finite n))] at 1;rewrite <- e.
 apply phi_of_psi_plus_finite.
 auto with T2.
 rewrite H3.
rewrite e.
 auto with T2.
intros (b1,(b2,(n,(H1,(H2,H3))))).
case (phi_cases' a Hc).
destruct 1.
case s;intros c1 (c2,(H'1,(H'2,H'3))).
 
rewrite H3;rewrite H'3;rewrite H'1.
subst b;
 subst c;case n;simpl;auto with T2.

constructor 2.
auto with T2.
apply le_lt_trans with  (cons b1 b2 0 (finite (S n))).
 simpl;auto with arith T2.
 auto with T2.
 constructor 2.
auto with T2.
 inversion H; auto with T2.
 lt_clean. 
 rewrite H3; rewrite e.
 apply transitivity with [a, (cons b1 b2 0 (finite (S n)))].
 case n;simpl;auto with T2.
 subst b;auto with T2.
intros (c1,(c2,(p,(H'1,(H'2,H'3))))).
rewrite H'3;rewrite H3.
subst c;subst b.
generalize H;inversion 1;auto with T2. 

constructor 3.
constructor 7.
apply lt_compatR.
 inversion H4;lt_clean; auto with T2.
Qed.



Lemma phi_mono_weak_r : forall a b c, nf a -> nf b -> nf c -> 
               b <= c -> phi a b <= phi a c. 
Proof.
 destruct 4.
 subst c;left;auto with T2.
 right; apply phi_mono_r;auto with T2.
Qed.

Lemma phi_inj_r : forall a b c, nf a -> nf b -> nf c ->
       phi a b = phi a c -> b= c.
Proof.
 intros a b c Na Nb Nc E.
tricho b c H.
absurd (phi a b < phi a c). 
rewrite E.
apply lt_irr.
apply phi_mono_r;auto.
auto.

absurd (phi a c < phi a b).
rewrite E.
apply lt_irr.
apply phi_mono_r;auto.
Qed.
 

Lemma lt_a_phi_ab : forall a b, nf a -> nf b -> a < phi a b.
Proof.
  intros.
  apply lt_le_trans with (phi a zero).
  apply no_critical.
  apply phi_mono_weak_r;auto with T2.
Qed.


(* Expressing psi in terms of phi 
   (as in Lepper-Moser) *)


Inductive is_successor : T2 -> Prop :=
 finite_succ : forall  n  , is_successor (cons zero zero n zero)
|cons_succ : forall a b n c, nf (cons a b n c) -> is_successor c ->
                               is_successor (cons  a b n c).



(* TO DO : make "is-limit" disappear : is_limit is better *)

  


Inductive is_limit : T2 -> Prop :=
|is_limit_0 : forall alpha beta n, zero < alpha \/ zero < beta ->
                 nf alpha -> nf beta -> is_limit (cons alpha beta n zero)
| is_limit_cons : forall alpha  beta n gamma, is_limit gamma ->
                                      nf (cons alpha beta n gamma) ->
                        is_limit (cons alpha beta n gamma). 

Lemma zero_not_lim : ~ (is_limit zero).
 red;inversion 1.
Qed.

Lemma F_not_lim : forall n, ~ is_limit (F n).
destruct n;red;inversion 1.
decompose [or] H3; lt_clean.
case  zero_not_lim;auto.
Qed.

Lemma is_succ_not_lim : forall alpha, is_successor alpha -> ~ is_limit alpha.
 induction alpha.
 intro;apply zero_not_lim.
 inversion_clear 1.
 apply (F_not_lim (S n)).
 red;inversion 1.
 subst alpha3;inversion H1. 
 case IHalpha3;auto. 
Qed.


Lemma is_limit_not_succ:  forall alpha, is_limit alpha -> ~ is_successor alpha.
 induction 1.
 red;inversion 1.
 subst alpha;subst beta.
 case H;intro;lt_clean.
inversion H8.
red;inversion 1.
 subst gamma.
 case zero_not_lim;auto.
 case IHis_limit.
 auto.
Qed.


(* 
   limit_plus_F alpha n beta  means :
   beta = alpha + F n and alpha is limit or alpha = zero 
*)



Inductive limit_plus_F : T2 -> nat -> T2 -> Prop :=
 limit_plus_F_0 : forall p, limit_plus_F zero p (F p)
|limit_plus_F_cons : forall beta1 beta2 n gamma0 gamma p,
                          zero < beta1 \/ zero < beta2 ->
                          limit_plus_F gamma0 p gamma ->
                          limit_plus_F (cons beta1 beta2 n gamma0)
                                        p (cons beta1 beta2 n gamma).

Lemma limit_plus_F_plus : forall alpha alpha' p,
                      limit_plus_F alpha p alpha' ->
                      nf alpha ->
                      alpha' = alpha + F p.
 induction alpha.
 inversion_clear 1.
 simpl;auto.
 inversion_clear 1.
 generalize (IHalpha3 gamma p).
 intros.
 rewrite (H H1).
 simpl.
 case p;simpl.
 rewrite plus_alpha_0;trivial.
 caseEq (compare [alpha1, alpha2] [zero, zero]).
 intro H3; generalize (compare_eq_rw H3).
 injection 1;intros;subst alpha1;subst alpha2.
 decompose [or] H0; lt_clean.
 intro H3; generalize (compare_lt_rw H3).
 inversion_clear 1;try lt_clean.
 auto.
 nf_inv.
Qed.




Lemma limit_plus_F_lim : forall alpha alpha' p,
                      limit_plus_F alpha p alpha' ->
                      nf alpha ->
                      is_limit alpha \/ alpha=zero.
Proof.
 intro alpha;elim alpha.
 auto.
 intros alpha1 _ alpha2 _ alpha3; case alpha3.
 left.
 inversion H0.
 case (H _ _ H9).
 nf_inv. 
 constructor.
 auto.
 auto.
 intro H18;rewrite H18;constructor 1;auto.
 nf_inv.
 nf_inv.
 left.
 
  inversion H0.
 case (H _ _ H9).
 nf_inv.
  constructor.
 auto.
 auto.
 intro H10;rewrite H10;constructor;try nf_inv.
 auto.
Qed.



Lemma limit_plus_F_inv0 : forall alpha beta,
                              limit_plus_F alpha 0 beta -> 
                              nf alpha -> alpha = beta.
Proof.
 intros.
 generalize (limit_plus_F_plus H H0).
 simpl.
 rewrite plus_alpha_0.
 auto.
Qed.

Lemma is_limit_cons_inv : forall b1 b2 n c, nf (cons b1 b2 n c) ->
                          is_limit (cons b1 b2 n c) -> is_limit c \/ c = zero.
Proof.
 inversion_clear 1;auto.
 inversion 1;auto.
Qed.

 
Lemma is_limit_intro : forall b1 b2 n , nf b1 -> nf b2 ->
                       zero < b1 \/ zero < b2 ->
                       is_limit  (cons b1 b2 n zero).
Proof.
 constructor;auto.
Qed.



Lemma lt_epsilon0_ok : forall alpha, nf alpha -> lt_epsilon0 alpha ->
                                     alpha < epsilon0.
Proof.
 induction 1;intros; compute;auto with T2.
 inversion_clear H1.
 constructor 2.
 auto with T2.
 apply IHnf2;auto with T2.
 inversion_clear H3.
 constructor 2;auto with T2.
Qed.


Derive Inversion_clear lt_01 with (forall (a b:T2),
                cons a b 0 zero <  epsilon0) Sort Prop.

Derive Inversion_clear lt_02 with (forall (a b c:T2)(n:nat),
                cons a b n c <  epsilon0) Sort Prop.

Lemma psi_lt_epsilon0 : forall a b, [a, b] < epsilon0 ->
       a = zero /\ b < epsilon0.
Proof.
 intros a b H.
 inversion H using lt_01.
 split.
 apply lt_one_inv;auto with T2.
 compute;auto with T2.
 inversion 1.
 inversion 2.
 inversion 1.
 inversion 1.
Qed.

Lemma cons_lt_epsilon0 : forall a b n c, cons a b n c < epsilon0 ->
       nf (cons a b n c) ->
       a = zero /\ b < epsilon0 /\ c < epsilon0.
Proof.
 intros a b n c H.
 inversion H using lt_02.
 split.
 apply lt_one_inv;auto with T2.
 split.
 unfold epsilon0.
 exact H1.
 apply transitivity with (cons a b n c);auto with T2.
 apply lt_tail;auto with T2.
 inversion 1.
 inversion 2.
 inversion 1.
 inversion 1.
Qed.



Lemma lt_epsilon0_okR: forall alpha, nf alpha -> alpha < epsilon0 ->
                                          lt_epsilon0 alpha.
Proof.
 induction alpha.
 constructor.
 unfold epsilon0;intros.
 inversion H0.
 rewrite (lt_one_inv H3).
 right.
 apply IHalpha2.
 inversion H;auto with T2.
 compute;auto with T2.
 apply IHalpha3.
 inversion H;auto with T2.
 compute;auto with T2.
 apply transitivity with (cons alpha1 alpha2 n alpha3).
 apply lt_tail.
 auto with T2.
 auto with T2.
 inversion H2.
 inversion H10.
 inversion H2.
 inversion H2.
Qed.





Lemma T1_injection : forall c c', T1_inj c = T1_inj c' -> c = c'.
Proof.
 induction c; destruct c';simpl;auto with T2.
 discriminate 1.
 discriminate 1.
 injection 1;auto with T2.
 rewrite (IHc1 c'1).
 rewrite (IHc2 c'2).
 destruct 2;auto with T2.
 injection H;auto with T2.
 injection H;auto with T2.
Qed.



 
Lemma T1_injection_lt : forall c, lt_epsilon0 (T1_inj c).
Proof.
 induction c;simpl;constructor;auto with T2.
Qed.



Definition lt_T1_injection : forall a, lt_epsilon0 a -> {c:T1 | T1_inj c = a}.
Proof.
 induction a.
 exists EPSILON0.zero;simpl;auto with T2.
 intro.
 case IHa2.
 inversion H;auto with T2.
 intros c2 e2.
 case IHa3.
 inversion H;auto with T2.
 intros c3 e3.
 exists (EPSILON0.cons c2 n c3).
 rewrite <- e3;rewrite <- e2.
 replace a1 with zero.
 simpl;auto with T2.
 inversion H;auto with T2.
Defined.



Lemma inj_mono : forall c c', (c < c')%ca -> T1_inj c < T1_inj c'.
Proof.
 induction 1;  simpl;auto with T2.
Qed.



(*
  In the following proof, some new tactics must make shorter the use
  of total order on cpnf.

*)

Lemma inj_monoR : forall c c', lt (T1_inj c) (T1_inj c') -> (c < c')%ca.
Proof.
 intros.
 case (EPSILON0.trichotomy_inf c c').
 destruct 1.
 auto with T2.
 subst c'.
 case (lt_irr H).
 intro.
 generalize (inj_mono l).
 intro.
 case (lt_irr (alpha:=T1_inj c)).
 eapply transitivity;eauto with T2.
Qed.


Lemma lt_epsilon0_trans : forall a, lt_epsilon0 a ->  nf a ->
     forall b, lt b a -> nf b -> lt_epsilon0 b.

Proof.
 intros.
 apply lt_epsilon0_okR.
 auto with T2.
 apply transitivity with a.
 auto with T2.
 apply lt_epsilon0_ok;auto with T2.
Qed.

Lemma nf_nat_irrelevance : forall a b n n' c, nf (cons a b n c) -> 
                                              nf (cons a b n' c).
Proof.
   inversion_clear 1;   constructor;auto with T2.
Qed.


Lemma psi_principal : forall a b c d, nf c -> c < [a, b] 
                                           -> d < [a, b] -> 
                                          c + d < [a, b].
Proof.
 induction c;destruct d;simpl;auto with T2.
 case (compare [c1,c2][d1,d2]).
 intros;apply psi_relevance.
 inversion_clear H0.
 constructor 2;auto with T2.
 constructor 3;auto with T2.
 constructor 4;auto with T2.
 constructor 5;auto with T2.
 inversion H2.
 inversion H2.
auto with T2.
 intros.
 generalize (IHc3 (cons d1 d2 n0 d3)).
 intros.
 assert (c3 < [a,b]).
 eapply transitivity.
 2:eexact H0.
 apply lt_tail.
 auto with T2.
 inversion_clear H0.
 constructor 2;auto with T2.
 constructor 3;auto with T2.
 constructor 4;auto with T2.
 constructor 5;auto with T2.
 inversion H4.
 constructor 7;auto with T2.
 inversion H4.
Qed.


 Lemma nf_intro : forall a b n c, nf a -> nf b -> 
                                  c < [a,b ] -> nf c -> nf (cons a b n c).
 Proof.
  destruct c;constructor;auto with T2.
  inversion_clear H1;auto with T2.
 inversion H3.
 inversion H3.
 Qed. 
 

Lemma plus_nf : forall alpha, nf alpha -> forall beta, nf beta -> 
                                    nf (alpha + beta).
 intros alpha Halpha.
 pattern alpha.
 apply transfinite_induction.
 destruct x.
 simpl;auto with T2.
 destruct beta.
 simpl;auto with T2.
 intros;simpl.
 caseEq ( compare (cons x1 x2 0 zero) (cons beta1 beta2 0 zero)).
 intro;apply nf_intro.
 nf_inv.
 nf_inv.
  generalize ( compare_eq_rw  H2).
 injection 1.
 intros; subst beta1; subst beta2.
 inversion_clear H1.
 auto with T2.
 apply psi_relevance;auto with T2.
 nf_inv.
 auto.
 intro;apply nf_intro.
 nf_inv.
 nf_inv.
 apply psi_principal.
 nf_inv.
 inversion H;auto.
 
 apply psi_relevance;auto with T2.
 apply psi_relevance;unfold psi; apply compare_gt_rw;auto with T2.
 eapply H0;auto with T2.
 nf_inv.
 apply lt_tail;auto with T2.
 assumption.
Qed.





Lemma succ_as_plus : forall alpha, nf alpha -> alpha + one = succ alpha.
 intro alpha;elim alpha.
 simpl;auto with T2.
 unfold one;simpl.
  intros.
case t; case t0.
 simpl.
 rewrite plus_0_r;auto with T2.
 simpl.
 rewrite <- H1.
 simpl;auto with T2.
 inversion H2;auto with T2.
  simpl.
  rewrite <- H1.
 simpl;auto with T2.
  inversion H2;auto with T2.
  simpl.
rewrite <- H1.
 simpl;auto with T2.
  inversion H2;auto with T2.  
Qed.


Lemma succ_nf : forall alpha, nf alpha -> nf (succ alpha).
Proof.
  intros alpha Halpha.
  rewrite <- succ_as_plus;auto with T2.
 apply plus_nf;auto with T2.
 compute; constructor;auto with T2.
Qed.





 

Lemma lt_epsilon0_succ : forall a, lt_epsilon0 a -> lt_epsilon0  (succ a).
 induction a.
 simpl.
 repeat constructor.
 simpl.
 case a1.
 case a2.
 repeat constructor.
 constructor.
 inversion H;auto with T2.
 apply IHa3.
 inversion H;auto with T2.
 inversion 1.
Qed.


Theorem epsilon0_as_lub : forall b, nf b -> 
                                    (forall a, lt_epsilon0 a -> lt a b) ->
                                    le epsilon0 b.
Proof.
 intros y Vy Hy.
 tricho epsilon0 y H.
 right;auto with T2.
 left;auto with T2.
 assert (lt_epsilon0 y).
 apply lt_epsilon0_okR;auto with T2.
 generalize (Hy _ H0).
 intro; case (lt_irr (alpha:= y)).
 auto with T2.
Qed.



(* TO DO :  define glb too *)


Definition lub (P:T2 -> Prop)(x:T2) :=
  nf x /\ 
  (forall y, P y -> nf y -> y <= x) /\
  (forall y, (forall x, P x -> nf x -> x <= y) -> nf y ->
                                    x <= y).

Theorem lub_unicity : forall P l l', lub P l -> lub P l' -> l = l'.
Proof.
 intros P l l' (H1,(H2,H3)) (H'1,(H'2,H'3)).
 
 tricho l l' H4.
 absurd (l < l).
 apply lt_irr.
 apply lt_le_trans with l';auto with T2.
 auto with T2.
 absurd (l' < l').
 apply lt_irr.
 apply lt_le_trans with l;auto with T2.
Qed.


Theorem lub_mono : forall (P Q :T2 -> Prop) l l', 
                                  (forall o, nf o -> P o -> Q o) ->
                                    lub P l -> lub Q l' -> l <= l'.
Proof.
 intros P Q l l' H (H1,(H2,H3)) (H'1,(H'2,H'3)).
 auto with T2.
Qed.


(* Change into suc_as_glb (see Ord_Complete.v) *)
(*
Theorem suc_as_lub : forall o, nf o -> lub (fun x => x = o) (succ o).
Proof.
 unfold lub;intros.
 repeat split.
 apply succ_nf;auto with T2.
  destruct 1. 
 intros;apply lt_succ.
 
 intros.
 apply lt_succ_le; auto with T2.
Qed.
*)


Lemma succ_limit_dec : forall a, nf a ->
         {a = zero} +{is_successor a}+{is_limit a}.
Proof.
 intro a;elim a.
left;left;auto.
 intro alpha;case alpha;intro.
 intro beta;case beta;intro.
 intros.
 assert (t=zero). inversion H2;auto.
 inversion H7;lt_clean.
 subst t;left;right.
constructor.
 destruct n0;destruct t2.
 right;constructor.
 auto.
 auto with T2.
 nf_inv.
 intros H1 H2;case H1.
 nf_inv.
 destruct 1.
 discriminate e.
left;right.
constructor;auto.
 right.
 constructor.
 auto.
 auto.
 right.
 constructor;auto.
 auto with T2.
 nf_inv.
 intros H1 H2;case H1.
 nf_inv.
 destruct 1.
 discriminate e.
 left;right;constructor.
 auto.
 auto.
 right;constructor;auto.
 intros.  case H1.
 nf_inv.
 destruct 1.
 subst t3;right;constructor;auto.
 nf_inv.
 nf_inv.
 left;right;constructor;auto.
 right;constructor;auto.
Qed.

 
Lemma le_plus_r : forall alpha beta, nf alpha -> nf beta -> 
                                     alpha <= alpha + beta.
Proof.
 induction alpha.
 intros;apply le_zero_alpha.
 destruct beta.
 intros; rewrite plus_alpha_0;auto with T2.
 simpl.
 intros; 
   caseEq( compare (cons alpha1 alpha2 0 zero) (cons beta1 beta2 0 zero)).
 right;constructor 6.
 omega.
 intros;right;apply psi_relevance.
 apply compare_lt_rw.
 auto with T2.
 intro; apply le_cons_tail.
 apply IHalpha3.
 inversion H;auto with T2.
 auto with T2.
Qed.


Lemma le_plus_l : forall alpha beta, nf alpha -> nf beta -> 
                                     alpha <= beta +  alpha.
Proof.
 induction alpha.
 intros;apply le_zero_alpha.
 destruct beta.
 simpl;auto with T2.
 simpl.
 intros; 
   caseEq(compare (cons beta1 beta2 0 zero) (cons alpha1 alpha2 0 zero)).
 intros.
 generalize (compare_eq_rw  H1).
injection 1.
 intros;subst beta1;subst beta2.
 
 right;constructor 6.
 omega.
 left;auto with T2.
 
 intros;right;apply psi_relevance.
 apply compare_gt_rw.
 auto with T2.
Qed.


Lemma plus_mono_r : forall alpha , nf alpha -> forall beta gamma, nf beta ->
       nf gamma -> beta < gamma -> alpha + beta < alpha + gamma.
Proof.
 induction alpha.
 simpl.
 auto with T2.
 simpl.
 destruct beta;destruct gamma;simpl.
 inversion 3.
 intros; 
   caseEq (compare (cons alpha1 alpha2 0 zero) (cons gamma1 gamma2 0 zero)).
 constructor 6. 
 omega.
 intros;apply psi_relevance.
 apply compare_lt_rw;auto with T2.
 constructor 7.
 pattern alpha3 at 1; rewrite <- plus_alpha_0. 
 apply IHalpha3.
 inversion H;auto with T2.
 auto with T2.
 auto with T2.
 auto with T2.
 inversion 3.
 caseEq (compare (cons alpha1 alpha2 0 zero) (cons beta1 beta2 0 zero));
 caseEq ( compare (cons alpha1 alpha2 0 zero) (cons gamma1 gamma2 0 zero)).
 intros.
  generalize (compare_eq_rw  H1).
  generalize (compare_eq_rw  H0).
injection 1.
injection 3.
 subst gamma1;subst gamma2;intros; subst beta2;subst beta1.
 inversion_clear H4.
 case (lt_irr H6).
 case (lt_irr H6).
 case (lt_irr H6).
 case (lt_irr H6).
 constructor 6;omega.
 constructor 7;auto with T2.
intros.
 generalize (compare_lt_rw  H0).
 generalize (compare_eq_rw  H1).
 intros;apply psi_relevance.
 auto with T2.
intros.
 generalize (compare_gt_rw  H0).
 generalize (compare_eq_rw  H1).
 injection 1;intros.
 subst beta1;subst beta2.
 case (lt_irr (alpha := (cons alpha1 alpha2 n0 beta3))).
 eapply transitivity.
 eexact H4.
 apply psi_relevance;auto with T2.
intros.
 generalize (compare_lt_rw  H1).
 generalize (compare_eq_rw  H0).
  injection 1;intros.
 subst gamma1;subst gamma2.
  case (lt_irr (alpha :=cons beta1 beta2 n0 beta3)).
 eapply transitivity.
 eexact H4.
  apply psi_relevance;auto with T2.
auto with T2.
intros.
 case (lt_irr (alpha := (cons beta1 beta2 n0 beta3))).
 eapply transitivity.
 eexact H4.
 apply psi_relevance.
apply transitivity with (cons alpha1 alpha2 0 zero);auto with T2.

intros.
  generalize (compare_eq_rw  H0).
injection 1;intros;subst gamma1;subst gamma2.
constructor 6;omega.
intros.
apply psi_relevance.
auto with T2.

intros.
constructor 7.
apply IHalpha3.
inversion H;auto with T2.
auto with T2.
auto with T2.
auto with T2.
Qed.


Lemma plus_mono_l_weak: 
 forall o, nf o ->
          forall alpha,  nf alpha -> alpha < o -> 
     forall beta,
       nf beta -> beta < o ->  forall gamma , nf gamma -> (* gamma <= o -> *)
         alpha < beta -> alpha + gamma <= beta  + gamma.
 intros o Ho;pattern o.
apply transfinite_induction.

2:auto with T2.
clear o Ho.
intros o NF0 Hreco. 


intro x;case x.

simpl.
intros;apply le_plus_l;auto with T2.

 
intros alpha beta n gamma NF.
intro.
intro y;case y.

inversion 4.

intros alpha' beta' n' gamma' NF'.
intros H1  z.
case z.
do 2 rewrite (plus_alpha_0).

right;auto with T2.

intros alpha'' beta'' n'' gamma''  NF''.
intros H0.

simpl (cons alpha beta n gamma + cons alpha'' beta'' n'' gamma'').
caseEq ( compare [alpha, beta] [alpha'', beta'']).
intro H'; generalize  (compare_eq_rw  H'); intro H''.
injection H'';intros. subst alpha'';subst beta''.
 simpl (cons alpha' beta' n' gamma' + cons alpha beta n'' gamma'').
 caseEq ( compare [alpha', beta'] [alpha, beta]).

intro H6; generalize  (compare_eq_rw  H6); intro H7.
injection H7;intros;subst alpha';subst beta'.
case (le_inv_nc (or_intror _ H0)).
right;constructor 6.
auto with T2 arith.
intros (H8,H9);subst n'.
left;auto with T2.

intro H6; generalize  (compare_lt_rw  H6); intro H7.
case (lt_irr (alpha := cons alpha beta n gamma)).
apply transitivity with (cons alpha' beta' n' gamma');auto with T2.
apply psi_relevance;auto with T2.

intros;right;apply psi_relevance.
apply compare_gt_rw;auto with T2.

intro H'; generalize  (compare_lt_rw  H'); intro H''.

 simpl (cons alpha' beta' n' gamma' + cons alpha'' beta'' n'' gamma'').
 caseEq (compare [alpha', beta'] [alpha'', beta'']).
intro H6; generalize  (compare_eq_rw  H6); intro H7.
injection H7;intros;subst alpha';subst beta'.
right;constructor 6;auto with T2 arith.

intro H6; generalize  (compare_lt_rw  H6); intro H7.
left;auto with T2.

intro H6; generalize  (compare_gt_rw  H6); intro H7.

right;apply psi_relevance;auto with T2.

intro H'; generalize  (compare_gt_rw  H'); intro H''.

assert ([alpha'',beta''] < [alpha',beta']).
apply lt_le_trans with [alpha,beta];auto with T2.
generalize (le_psi_term_le (or_intror _ H0)).
simpl;auto with T2.
simpl ( cons alpha' beta' n' gamma' + cons alpha'' beta'' n'' gamma'').
caseEq ( compare [alpha', beta'] [alpha'', beta'']).

intro H6; generalize  (compare_eq_rw  H6); intro H7.
rewrite H7 in H2.
case (lt_irr H2).

intro H6; generalize  (compare_lt_rw  H6); intro H7.
case (lt_irr (alpha := [alpha'', beta''])).
apply transitivity with [alpha', beta'];auto with T2.


intro H6; generalize  (compare_gt_rw  H6); intro H7.

tricho [alpha, beta] [alpha', beta'] H8.
right;apply psi_relevance;auto with T2.
injection H8;intros;subst alpha';subst beta'.
case (le_inv_nc  (or_intror _ H0)).
right;constructor 6;auto with T2.
intros (e,H9);subst n'.
case H9.
intro;subst gamma'.
left;auto with T2.
intro H10.

assert (nf gamma).
inversion NF;auto with T2.

assert (nf gamma').
inversion NF';auto with T2.


assert (gamma <  cons alpha beta n gamma').
apply transitivity with gamma'.
auto with T2.
apply lt_tail;auto with T2.





generalize (Hreco  _ NF' H1 gamma H3 H5 gamma' H4 (lt_tail NF')
  (cons alpha'' beta'' n'' gamma'') NF'' H10).
destruct 1;auto with T2.
rewrite H11;auto with T2.

case (lt_irr (alpha := cons alpha beta n gamma)).
apply transitivity with (cons alpha' beta' n' gamma');auto with T2.
apply psi_relevance;auto with T2.
Qed.

Remark R_predD_0 : pred zero = None.
 trivial.
Qed.


Remark R_pred_Sn : forall n, pred (F (S n)) = Some (F n).
 destruct n;simpl;trivial.
Qed.

Lemma pred_of_cons : forall a b n c, 
                       zero < a \/ zero < b -> 
                       pred (cons a b  n c) = match pred c with
                                             Some c' => 
                                               Some (cons a b n c')
                                            |None => None
                                            end.
  destruct a.
 destruct b;simpl.
 destruct 1;lt_clean.
 auto.
 simpl.
 auto.
Qed.

Lemma pred_of_cons' : forall a b n , 
                       zero < a \/ zero < b -> 
                       pred (cons a b  n zero) = None.
Proof.
 intros a b n H; rewrite (pred_of_cons n zero H).
 simpl;auto.
Qed.

Lemma is_limit_ab : forall alpha beta n gamma, is_limit (cons alpha beta n gamma)
  -> zero < alpha \/ zero < beta.
inversion 1.
 auto.
 generalize H5 H2 ;case gamma.
  inversion 2.

 inversion_clear 1.
 

 inversion_clear H7.  
 left;apply le_lt_trans with t;auto with T2.
 right; apply le_lt_trans with t0;auto with T2.
 right;  apply le_lt_trans with [t,t0];auto with T2.
 right;apply le_lt_trans with t;auto with T2.
 lt_clean.
 lt_clean.
Qed.

 
 

Lemma pred_of_limit : forall alpha,  is_limit alpha -> nf alpha -> pred alpha = None.
Proof.
 induction 1.
 rewrite (pred_of_cons' n H).
 auto.
 rewrite (pred_of_cons (a :=alpha)(b:=beta) n).
 rewrite IHis_limit.
auto.
 eapply nf_c;eauto.
apply is_limit_ab with n gamma.
constructor;auto.
Qed.
 


Lemma pred_of_succ : forall alpha, nf  alpha -> 
            pred (succ alpha) = Some alpha.
 induction alpha;simpl.
 auto with T2.
 case alpha1;case alpha2.
 simpl.
 inversion_clear 1;auto with T2.
 inversion H0.
 inversion H5.
 inversion H4.
 inversion H12.
 inversion H4.
 inversion H4.
 simpl.

 intros;rewrite IHalpha3.
 auto with T2.
 inversion H;auto with T2.
 simpl.
 intros;rewrite IHalpha3.
 auto with T2.
 inversion H;auto with T2.
 simpl.
  intros;rewrite IHalpha3.
 auto with T2.
 inversion H;auto with T2.
Qed.




Lemma limit_plus_F_ok : forall alpha,  is_limit alpha ->
                           forall n, limit_plus_F alpha n (alpha + F n).
Proof.

induction alpha.
simpl;constructor 1.
simpl.
inversion 1.
intro n1;case n1.
 simpl.
 constructor 2;auto.
 change (limit_plus_F zero 0 (F 0)).
 
 constructor 1.
 simpl.
 caseEq (compare [alpha1, alpha2] [zero, zero]).
 intro H7; generalize (compare_eq_rw H7).
 injection 1;intros;subst alpha1;subst alpha2.
 subst alpha;subst beta.
 case H3;intro;lt_clean.
 
  intro H7; generalize (compare_lt_rw H7).
 inversion 1;intros;try lt_clean.
 simpl.
 intros.
 change (limit_plus_F (cons alpha1 alpha2 n zero) (S n2)
     (cons alpha1 alpha2 n (F (S n2)))).
 constructor.
 auto.
 constructor.

 destruct n1.
 simpl.
 
 constructor 2.
 eapply is_limit_ab.
 eexact H.
 generalize H2.
 generalize (nf_c H5).
 elim alpha3.
 intros; change ( limit_plus_F zero 0 (F 0));constructor.
 constructor.
 eapply is_limit_ab.
 eexact H10.
 case (is_limit_cons_inv H9 H10).
 intros.
 
 apply H8.
 nf_inv.
 auto.
 intro;subst t1;change (limit_plus_F zero 0 (F 0));constructor.
simpl.
 caseEq (compare [alpha1, alpha2] [zero, zero]).
 intro H7;generalize (compare_eq_rw H7);injection 1;intros.
 subst alpha1;subst alpha2;subst beta;subst alpha.
 generalize (is_limit_ab H).
 destruct 1;lt_clean.
 intro H7;generalize (compare_lt_rw H7);intros.
 inversion H6;lt_clean.
 intro.
 replace (cons zero zero n1 zero) with (F (S n1)).
 constructor 2.
 generalize (compare_gt_rw H6);intros.
 inversion_clear H7;auto with T2.
 lt_clean.
 lt_clean.
 apply IHalpha3.
 auto.
 auto.
Qed.






 
Section phi_to_psi.
 Variable alpha : T2.

 Lemma phi_to_psi_1 : forall beta1 beta2 n, 
                             alpha < beta1 -> 
                             [alpha, (cons beta1 beta2 0 (F n))] =
                             phi alpha (cons beta1 beta2 0 (F (S n))).
 Proof.
   intros.
   generalize (phi_of_psi_succ alpha beta1 beta2 n).
 case (lt_ge_dec alpha beta1).
 auto with T2.
 intro.
 (* TODO : a thm lt_not_ge *)
 absurd (alpha < alpha).
 apply lt_irr.
 eapply lt_le_trans;eauto with T2.
 Qed.

 Lemma phi_to_psi_2 : forall beta1 beta2 n, 
                             beta1 <= alpha  -> 
                             [alpha, (cons beta1 beta2 0 (F n))] =
                             phi alpha (cons beta1 beta2 0 (F n)).
   intros.
   case n.
  simpl (F 0).
    generalize (phi_of_psi alpha beta1 beta2).
    case (lt_ge_dec alpha beta1).
    intro; (absurd (alpha<alpha)). 
   (* Argh *)
    apply lt_irr.
    eapply lt_le_trans;eauto with T2.
  auto with T2.

   intro n0;generalize (phi_of_psi_succ alpha beta1 beta2 n0).
 case (lt_ge_dec alpha beta1).
 2:auto with T2.
  intro;  absurd (alpha < alpha).
 apply lt_irr.
 eapply lt_le_trans;eauto with T2.
 Qed.

 Lemma phi_to_psi_3 : forall  beta1 beta2 , 
                             beta1 <= alpha  -> 
                             [alpha, [beta1, beta2]] =
                             phi alpha [beta1, beta2].
 Proof.
   intros. 
   fold (F 0).
   apply phi_to_psi_2.
 auto with T2.
Qed.

Lemma phi_to_psi_4 : [alpha, zero] = phi alpha zero.
Proof.
  rewrite phi_alpha_zero;auto with T2.
Qed.

Lemma phi_to_psi_5 :
   forall beta1 beta2 n gamma, omega <= gamma \/ (0 < n)%nat ->
           [alpha,cons beta1 beta2 n gamma] =
           phi alpha (cons beta1 beta2 n gamma).
Proof.
 intros.
  rewrite phi_of_any_cons;auto with T2.
Qed.

Lemma phi_to_psi_6 : forall beta, nf beta ->
   phi alpha beta = beta -> [alpha,  beta] =phi alpha (succ beta).
 intros.
 case (phi_fix _ H0 ).
 intros beta1 (beta2,(H2,H3)).
 subst beta.
generalize (phi_to_psi_1 beta2  0 H3).  
  simpl (succ (cons beta1 beta2 0 zero)).
 generalize H3 ; case beta1.
 inversion 1.
 auto with T2.
Qed.


(* gamma = gamma0 + F p, gamma0 = zero or gamma0 limit *)

(* simplify this proof !!!!! *)
 
Lemma phi_psi : forall  beta0 beta n, nf beta ->
  limit_plus_F beta0 n beta ->  phi alpha beta0 = beta0 ->
                           [alpha, beta]  =  phi alpha (succ beta).
 intros.
 case (phi_fix _ H1).
 intros beta1 (beta2,(H2,H3)).
 assert (beta = (cons beta1 beta2 0 (F n))).
 Focus 2.
 subst beta.
 simpl.
 subst beta0.
 generalize H3 H1.
 case beta1;case beta2.
 inversion 1.
 inversion 2.
 inversion H2.
 replace (succ (F n)) with (F (S n)).
 intros;rewrite phi_to_psi_1.
 auto with T2.
 auto with T2.
 induction n;simpl;auto with T2.
 replace (succ (F n)) with (F (S n)).
 intros;rewrite phi_to_psi_1.
 auto with T2.
 auto with T2.
  induction n;simpl;auto with T2.
subst beta0.
 inversion H0.
 inversion H9.
 auto with T2.
 inversion H10.
 auto with T2.
 inversion H10;auto with T2.
Qed.



Theorem th_14_5 : forall alpha1 beta1 alpha2 beta2,
                   nf alpha1 -> nf beta1 -> nf alpha2 -> nf beta2 ->
                   phi alpha1 beta1 = phi alpha2 beta2 ->
                   {alpha1 < alpha2 /\ beta1 = phi alpha2 beta2} +
                   {alpha1 = alpha2 /\ beta1 =  beta2} +
                   {alpha2 < alpha1 /\ phi alpha1 beta1 = beta2}.
Proof.
 intros alpha1 beta1 alpha2 beta2 nfa1 nfb1 nfa2 nfb2 E.
 tricho alpha1 alpha2 H0.
 generalize (phi_to_psi alpha2 beta2).
  intros (gamma1, (gamma2, E')).
 assert (alpha2 <= gamma1).
 eapply phi_le.
 2:eexact E'.
 auto.
 left.
 left;split;auto.
 assert (phi alpha1 (phi alpha2 beta2) = phi alpha2 beta2).
 repeat rewrite E'.
 simpl.
 generalize (lt_le_trans H0 H);intro H1.
 rewrite (compare_rw_lt H1).
 auto.
 pattern (phi alpha2 beta2) at 2 in H1.
 rewrite <- E in H1.
 apply phi_inj_r with alpha1;auto.
 apply phi_nf;auto.
 subst alpha2.
 left.
 right.
 split;auto.
 apply phi_inj_r with alpha1;auto.
 generalize (phi_to_psi alpha1 beta1).
 intros (gamma1, (gamma2, E')).
 assert (alpha1 <= gamma1).
 apply phi_le with beta1 gamma2.
 auto.
 auto.
 right. 
 split;auto.
 assert (phi alpha2 (phi alpha1 beta1) = phi alpha1 beta1).
 repeat rewrite E'.
 simpl.
 generalize (lt_le_trans H0 H);intro H1.
 rewrite (compare_rw_lt H1).
 auto.
 pattern (phi alpha1 beta1) at 2 in H1.
 rewrite E in H1.
 apply phi_inj_r with alpha2;auto.
 apply phi_nf;auto.
Qed.

Lemma lt_not_gt : forall a b, a < b -> ~ (b < a).
Proof.
  intros a b H H0.
  case (lt_irr (alpha := a));auto.
  apply transitivity with b;auto.
Qed.

Lemma phi_mono_RR : forall a b c, nf a -> nf b -> nf c ->
              phi a b < phi a c -> b < c.
 Proof.
  intros;tricho b c T;auto.
  subst c. case (lt_irr H2).
  case (lt_not_gt H2).
  apply phi_mono_r;auto.
 Qed.

Theorem th_14_6 : forall alpha1 beta1 alpha2 beta2,
                   nf alpha1 -> nf beta1 -> nf alpha2 -> nf beta2 ->
                   phi alpha1 beta1 < phi alpha2 beta2 ->
                   {alpha1 < alpha2 /\ beta1 < phi alpha2 beta2} +
                   {alpha1 = alpha2 /\ beta1 <  beta2} +
                   {alpha2 < alpha1 /\ phi alpha1 beta1 < beta2}.
Proof.
 intros alpha1 beta1 alpha2 beta2 nfa1 nfb1 nfa2 nfb2 E.
 tricho alpha1 alpha2 H0.
 generalize (phi_to_psi alpha2 beta2).
  intros (gamma1, (gamma2, E')).
 assert (alpha2 <= gamma1).
 eapply phi_le.
 2:eexact E'.
 auto.
 left.
 left;split;auto.
 apply le_lt_trans with (phi alpha1 beta1);auto.
 apply le_b_phi_ab;auto.
 subst alpha2.
left;right.
 split;auto.
 tricho beta1 beta2 H;auto.
 subst beta2;case (lt_irr E).
 case (lt_not_gt E).
 apply phi_mono_r;auto.
 right. 
 split;auto. 
 generalize (phi_to_psi alpha1 beta1).
 intros (gamma1, (gamma2, E')).
 assert (alpha1 <= gamma1).
 apply phi_le with beta1 gamma2.
 auto.
 auto.
 assert (alpha2 < gamma1).
 apply lt_le_trans with alpha1;auto.

 assert (phi alpha2 (phi alpha1 beta1) = phi alpha1 beta1).
 repeat rewrite E'.
 simpl.
 rewrite (compare_rw_lt H1).
 auto.

 assert (phi alpha2 (phi alpha1 beta1) < phi alpha2 beta2).
 eapply le_lt_trans.
 eleft;eexact H2.
 auto.
 apply phi_mono_RR with alpha2;auto.
 apply phi_nf;auto.
Qed.


(* First admitted lemma !!!!!! *)

Definition moser_lepper (beta0 beta:T2)(n:nat) :=
 limit_plus_F beta0 n beta /\ phi alpha beta0 = beta0.

Lemma ml_psi : forall beta0 beta n, moser_lepper beta0 beta n ->
                                    {t1 : T2 & {t2: T2| beta0 = [t1,t2] /\ alpha < t1}}.
Proof.
 intros beta0 beta n (H1,H2).
 case (phi_fix  _  H2).
 intros x (y,(H3,H4)).
 exists x;exists y;auto.
Qed.

Lemma ml_1 : forall beta0 beta n, moser_lepper beta0 beta n -> nf beta -> nf beta0 ->
                               [alpha, beta] = phi alpha (succ beta).
 intros;eapply phi_psi;eauto.
 case H.
 intros;eassumption.
 case H;intros.
 auto.
Qed.


 
                                                          
End phi_to_psi.








 


