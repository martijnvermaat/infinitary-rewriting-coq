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


(*** Cantor "pre" Normal form
 After Manolios and Vroon work on ACL2 *)

Require Import Arith.
Require Import Omega. (* ( :-) *)
Require Import Compare_dec.
Require Import Relations.
Require Import Wellfounded.

Require Import Tools.
Require Import More_nat.
Require Import Wf_nat.
Require Import AccP.
Require Import not_decreasing.
Require Import ArithRing.


Require Import term.
Require Import rpo.
Require Import List.




Set Implicit Arguments.


(************************)
(*   Definitions        *)
(************************)

(** cons a n b represents  omega^a *(S n)  + b *)

Inductive T1 : Set :=
  zero : T1
| cons : T1 -> nat -> T1 -> T1.


(** some abreviations *)
(*********************)

(** omega^x * (S k) *)

Definition omega_term (a:T1)(k:nat) :=
   cons a k zero.

Definition phi0 a := cons a 0 zero.


Definition finite (n:nat) : T1 :=
 match n with  0 => zero
             | S p => cons zero p zero
         end.

Notation "'F' n" := (finite n)(at level 29) : cantor_scope.

Definition omega := cons (cons zero 0 zero) 0 zero.

Definition log a := match a with
                               | zero => zero
                               | cons a _ _ => a
                              end.


Fixpoint omega_tower (n:nat) : T1 :=
            match n with 0 => finite 1
                       | S p => cons (omega_tower p) 0 zero
            end.


(* A total strict order on T1 *)


Inductive lt : T1 -> T1 -> Prop :=
|  zero_lt : forall a n b, lt zero  (cons a n b)
|  head_lt :
    forall a a' n n' b b', lt a  a' ->
                           lt (cons a n b) (cons a' n' b')
|  coeff_lt : forall a n n' b b', (n < n')%nat ->
                                 lt (cons a n b) (cons a n' b')
|  tail_lt : forall a n b b', lt b b' ->
                             lt (cons a n b) (cons a n b')
where  "o < o'" := (lt o o') : cantor_scope.

Hint Resolve zero_lt head_lt coeff_lt tail_lt : T1.

Open Scope cantor_scope.
Delimit Scope cantor_scope with ca.


(* the total non-strict order associated with lt   *)

Definition le (alpha beta :T1) := alpha = beta \/ alpha < beta.
Notation "alpha <= beta" := (le alpha beta) : cantor_scope.

Hint Unfold le : T1.



(* Additive principal ordinals *)

Inductive ap : T1 -> Prop:=
 ap_intro : forall a,  ap (cons a 0 zero).

Lemma ap_phi0 : forall a, ap (phi0 a).
Proof.
 unfold phi0;constructor.
Qed.

Lemma ap_phi0R : forall a, ap a ->{b : T1 | a = phi0 b}.
Proof.
  destruct a.
  intro;  elimtype False. 
  inversion H.
  exists a1.
  inversion H.
  unfold phi0;auto.
Qed.

Fixpoint compare (c c':T1){struct c'}:comparison :=
  match c,c' with
    zero, zero => Eq
  | zero, cons a' n' b' => Lt
  | _   , zero => Gt
  | (cons a n b),(cons a' n' b') =>
      (match compare a a' with
          | Lt => Lt
          | Gt => Gt
          | Eq => (match lt_eq_lt_dec n n' with
                                           inleft  (left _) => Lt
                                         | inright _ => Gt
                                         |   _ => compare b b'
                                         end)
      end)
 end.



Definition max a b := match compare a b with Lt => b | _ => a end.




(* Properties of lt *)
(**********************)



Theorem not_lt_zero : forall a, ~ a < zero.
Proof.
  red; inversion_clear 1.
Qed.

Hint Resolve not_lt_zero : T1.

Theorem lt_inv : forall a n b a' n' b',
                      cons a n b <  cons a' n' b' ->
                      a < a' \/
                      a = a' /\ (n < n')%nat \/
                      a = a' /\ n = n' /\ b < b'.
Proof.
 inversion_clear 1; auto.
Qed.


Theorem lt_irr : forall a, ~ a < a.
Proof.
 induction a.
 red;inversion_clear 1.
 intro H; case (lt_inv  H); intuition.
Qed.
Hint Resolve lt_irr : T1.


Lemma lt_inv_nb : forall a n n' b b',
                       cons a n b <  cons a n' b' ->
                       (n<n')%nat \/  n=n' /\ b < b'.
Proof.
 inversion_clear 1; auto with T1.
 elim (lt_irr (a:=a)); auto.  
Qed.

Lemma lt_inv_b : forall a n b b',
       cons a n b <  cons a n b' -> b < b'.
Proof.
 inversion_clear 1; auto with arith T1.
 elim (lt_irr  (a:=a));auto.
 elim (lt_irrefl n);auto.
Qed.

(* lt is a (strict) order *)

Theorem lt_trans : forall a b, a < b ->
                        forall c, b < c -> a < c.
Proof.
 induction 1.
 inversion 1; auto with T1.
 inversion_clear 1; auto with T1.
 inversion_clear 1; eauto with T1 arith.
 inversion_clear 1; auto with T1.
Qed.


Theorem lt_not_gt : forall a b, a < b  -> ~ b < a.
Proof.
 intros o1 o2 H H0.
 generalize (lt_trans  H H0).
 intro H2; case (lt_irr H2).
Qed.

Lemma finite_lt : forall n p : nat, (n < p)%nat ->
                      F n < F p.
Proof.
 destruct n;simpl.
 destruct p.
 inversion 1.
 simpl;auto with T1.
 destruct p.
 inversion 1.
 simpl;auto with T1.
 intro; assert (n<p)%nat ; auto with arith T1.
Qed.

Lemma finite_ltR : forall n p : nat,
                      F n < F p  ->
                      (n < p)%nat.
Proof.
 destruct n;simpl.
 destruct p.
 inversion 1.
 auto with arith.
 destruct p.
 inversion 1.
 simpl.
 intro H; case (lt_inv_nb H).
 auto with arith.
 intros (_,H0); case (lt_irr H0).  
Qed.




(* The predicate "to be in normal form" *)

(* The real Cantor normal form needs the exponents of omega to be
   in strict decreasing order *)


Inductive nf : T1 -> Prop :=
| zero_nf : nf zero
| single_nf : forall a n, nf a ->  nf (cons a n zero)
| cons_nf : forall a n a' n' b, a' < a ->
                             nf a ->
                             nf(cons a' n' b)->
                             nf(cons a n (cons a' n' b)).
Hint Resolve zero_nf single_nf cons_nf : T1.




(*  "nf2 b a "means "b less than omega^a" *)

Inductive nf2 : T1 -> T1 -> Prop :=
| nf2_z : forall a, nf2 zero a
| nf2_c : forall a a' n' b', a' < a ->
                             nf2 (cons a' n' b') a.

Hint Resolve nf2_z nf2_c : T1.


(* General properties of the predicate "to be in normal form" *)

(* inversion lemmas *)


Lemma nf_inv1 : forall a n b, nf (cons a n b) -> nf a.
Proof.
  inversion_clear 1; auto.
Qed.

Lemma nf_inv2 : forall a n b, nf (cons a n b) -> nf b.
Proof.
 inversion_clear 1; auto  with T1.
Qed.

Hint Resolve nf_inv1 nf_inv2 : T1.

Ltac nf_inv := (eapply nf_inv1; progress eauto)||
               (eapply nf_inv2; progress eauto).

Lemma nf_tail_lt_nf : forall  b b', b' < b -> nf b' ->
                          forall a n,   nf (cons a n b) ->
                                        nf (cons a n b').
Proof.
 induction 1.
 constructor; eauto with T1.
 constructor.
 apply lt_trans with a'; auto.
 inversion H1; eauto with T1.
 eauto with T1.
 assumption.
 constructor.
 inversion H1;eauto with T1.
 eauto with T1.
 assumption.
 constructor.
 inversion H1;eauto with T1.
 eauto with T1.
 assumption.
Qed.


Lemma tail_lt_cons : forall b n a,
     nf (cons a n b)->
     b < cons a n b.
Proof.
 induction b.
 constructor.
 constructor 2.
 inversion H;auto.
Qed.


(* the number n isn't so important in nf_ness *)

Lemma nf_intro : forall a n b, nf a ->
                               nf b ->
                               nf2 b a ->
                               nf (cons a n b).
Proof.
 destruct 3; constructor; auto.
Qed.


Lemma nf2_intro : forall a n b, nf (cons a n b) ->
                                nf2 b a.
Proof.
 inversion 1 ; constructor; auto.
Qed.


Lemma nf2_phi0 : forall a b, nf2 b a ->
                             b < phi0 a.
Proof.
  induction 1; compute;  auto with T1.
Qed.

Lemma nf2_phi0R : forall a b, b < phi0 a -> nf2 b a.
Proof.
  induction b.
  constructor.
 inversion_clear 1.
 constructor;auto.
 inversion H0.
 inversion H0.
Qed.

Lemma nf_coeff_irrelevance : forall a b n p, nf (cons a n b) ->
                                             nf (cons a p b).
Proof.
 intros; apply nf_intro; try nf_inv.
 eapply nf2_intro;eauto.
Qed.



  

Lemma log_nf : forall a, nf a -> nf (log a).
Proof.
 destruct a;unfold log;simpl.
 constructor; eauto with T1.
 eauto with T1.
Qed.
 

Lemma nf_of_finite : forall  n b, nf (cons zero n b) ->
                       b = zero.
Proof.
 intros n b H; inversion_clear H.
 trivial.
 case (not_lt_zero (a:=a'));auto.
Qed.

Lemma ordinal_finite : forall n, nf (F n).
Proof.
 unfold finite; intro n;case n; auto with T1 arith.
Qed.


Lemma nf_omega : nf omega.
Proof.
 unfold omega; auto with T1.
Qed.

Theorem nf_phi0 : forall a, nf a -> nf (phi0 a).
 compute;auto with T1.
Qed.

Lemma nf_tower : forall n, nf (omega_tower n).
 induction n; simpl; auto with T1.
Qed.


Definition nf_rect : forall P : T1 -> Type,
   P zero ->
   (forall n: nat,  P (cons zero n zero)) ->
   (forall a n b n' b', nf (cons a n b) ->
                        P (cons a n b)->
                        nf2 b' (cons a n b) ->
                        nf b' ->
                        P b' ->
                         P (cons (cons a n b) n' b')) ->
   forall a, nf a -> P a.
Proof.
 intros P H0 Hfinite Hcons.
 induction a.
 trivial.
 generalize IHa1;case a1.
 intros IHc0 H.
 rewrite (nf_of_finite H).
 apply Hfinite.
 intros c n0 c0 IHc0 H2; apply Hcons.
 eauto with T1.
 apply IHc0; eauto with T1.
 eapply nf2_intro. eauto. 
 nf_inv; eauto.
 apply IHa2. 
 nf_inv.
Defined.


Section lt_not_well_founded.
  
  (* let us build the sequence of terms :
        omega + omega + .... + omega ^ 2   *)
  Let f := (fix f (i:nat): T1 :=
            match i with 0 => (phi0 (F 2))
                       | S i => cons (F 1)  0 (f  i)
            end).


 Lemma f_not_in_normal_form :
  forall i, ~ (nf (f (S i))).
 Proof.
  induction i;  red; simpl.
  inversion 1.
  inversion H3.
  inversion H9.
  inversion H9.
  simpl in IHi.
  inversion 1.
  case (lt_irr H3).
 Qed.
 
 Lemma  f_decreases : forall i, f (S i) <  f i.
 Proof.
  induction i; compute; auto with T1.
 Qed.



 Theorem lt_not_wf : ~ (well_founded lt).
 Proof.
  red; intro wf.
  case (not_decreasing _ lt).
  auto.
 
  exists f.
  exact f_decreases.
 Qed.

End lt_not_well_founded.


Theorem zero_le : forall a, zero <= a.
Proof.
 unfold le.
 destruct  a; [left|right];repeat constructor.
Qed.


Theorem le_trans : forall a b c, a <= b -> b <= c -> a <= c.
Proof.
 destruct 1.
 subst b;auto.
 destruct 1.
 subst b;right;auto.
 right;eapply lt_trans;eauto.
Qed.


Theorem le_lt_trans : forall a b c, a <= b -> b < c -> a < c.
Proof.
 destruct 1.
 subst b;auto.
 intros;eapply lt_trans;eauto.
Qed.



Theorem lt_le_trans : forall a b c, a < b -> b <= c -> a < c.
Proof.
 destruct 2.
 subst b;auto.
 eapply lt_trans;eauto.
Qed.


Theorem le_inv : forall a n b a' n' b',
                      cons a n b <= cons a' n' b' ->
                      a < a' \/
                      a = a' /\ (n < n')%nat \/
                      a = a' /\ n = n' /\ b <= b'.
Proof.
 intros a n b a' n' b' H; case H.
 injection 1; right.
 right; subst a; subst n ; subst b; auto with T1.
 intro H0; generalize (lt_inv H0).
 intro H1; case H1; auto.
 intros [(H2,H3) | (H2,(H3,H4))].
 auto.
 right;right;auto with T1.
Qed.





Lemma lt_not_le: forall a b,  a < b -> ~  b <= a.
Proof.
 red; unfold le.
 intros a b H H0; case H0;intro.
 subst b; absurd (lt a a);auto with T1.
 absurd (lt a a); eauto with T1.
 eapply lt_trans;eauto.
Qed.



Lemma lt_inv_le : forall a n b a' n' b',
                     cons a n b < cons a' n' b' ->
                     a <= a'.
Proof.
 intros a n b a' n' b' H.
 case (lt_inv H).
 auto with T1.
 intros [(e,i)|(e,(e',i))].
 subst a; auto with T1.
 subst a; auto with T1.
Qed.


Theorem le_zero_inv : forall a, a <= zero -> a = zero.
Proof.
 destruct 1.
 auto.
 absurd (a < zero);auto with T1.
Qed.



Theorem le_tail : forall a n b b', b <= b' ->
                                   cons a n b <= cons a n b'.
Proof.
 destruct 1.
 subst b; left; auto.
 right; auto with T1.
Qed.

Hint Resolve zero_le le_tail : T1.


(* warning : this is NOT a general property of ALL ordinals *)
(* False when a >= epsilon_0
*)

Lemma head_lt_cons : forall a n b, a < cons a n b.
Proof.
 induction a.
 constructor.
 constructor 2; auto.
Qed.
 


Definition T1_eq_dec : forall (a b : T1), {a = b}+{a <> b}.
Proof.
 decide equality.
 apply eq_nat_dec.
Defined.  



Definition trichotomy_inf : forall a b, {a < b}+{a = b}+{b < a}.
Proof.
 induction a; destruct b; auto with T1.
 case (IHa1 b1);intros s.
 case s;intros.
 auto with T1.
 subst b1; case (lt_eq_lt_dec n n0).
 destruct 1.
 auto with T1.
 subst n;
  case (IHa2 b2); auto with T1.
 destruct 1;[idtac| subst b2];auto with T1.
 right;auto with T1.
 auto with T1.
Defined.


Definition max' a b :=
    if trichotomy_inf a b 
    then b else a.
(*


Definition max' a b :=
    match trichotomy_inf a b with
      inleft _ => b
    | _        => a
    end.
*)

Goal forall a b, a < b -> max' a b = b.
 intros a b H; unfold max'; 
   case (trichotomy_inf a b);auto.
   intro;case (lt_not_gt H);auto.
Qed.


 


Definition lt_le_dec : forall a b, {a < b}+{b <= a}.
Proof.
 intros a b; case (trichotomy_inf a b).
 destruct 1.
 left;auto.
 right;left; auto.
 right;right; auto.
Defined.





Module  Eps0_sig <: Signature.


Inductive symb0 : Set := nat_0 | nat_S | ord_zero | ord_cons.

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
                  | ord_cons => Free 3
                  end.

End Eps0_sig.

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

Module  Eps0_prec <: Precedence.

Definition A : Set := Eps0_sig.symb.
Import Eps0_sig.

Definition prec : relation A :=
   fun f g => match f, g with
                      | nat_0, nat_S => True
                      | nat_0, ord_zero => True
                      | nat_0, ord_cons => True
                      | ord_zero, nat_S => True
                      | ord_zero, ord_cons => True
                      | nat_S, ord_cons => True
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

End Eps0_prec.

Module Eps0_alg <: Term := term.Make (Eps0_sig) (Vars).
Module Eps0_rpo <: RPO := rpo.Make (Eps0_alg) (Eps0_prec).

Import Eps0_alg.
Import Eps0_rpo.
Import Eps0_sig.


Fixpoint nat_2_term (n:nat) : term :=
  match n with 0 => (Term nat_0 nil)
             | S p => Term nat_S ((nat_2_term p)::nil)
  end.



(** * Every (representation of a) natural number is less than
 a non zero ordinal *)

Lemma nat_lt_cons : forall (n:nat) a p  b , rpo (nat_2_term n) 
                                     (Term ord_cons (a::p::b::nil)).
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
 case (rpo_closure t2 t1 t);eauto.
Qed.


Fixpoint T1_2_term (a:T1) : term := 
match a with
 zero => Term ord_zero nil
|cons a n b => Term ord_cons (T1_2_term a :: nat_2_term n ::T1_2_term b::nil)
end.

Fixpoint T1_size (o:T1):nat :=
 match o with zero => 0
            | cons a n b => S (T1_size a + n + T1_size b)%nat
         end.

Lemma T1_size1 : forall a n b, (T1_size zero < T1_size (cons a n b))%nat.
Proof.
 simpl.
 intros.
 auto with arith.
Qed.

Lemma T1_size2 : forall a n b , (T1_size a < T1_size (cons a n b))%nat.
Proof.
 simpl; auto with arith.
Qed.

Lemma T1_size3 : forall a n b , (T1_size b < T1_size (cons a n b))%nat.
Proof.
 simpl; auto with arith.
Qed.

Hint Resolve T1_size2 T1_size3.


(** let us recall subterm properties on T1 *)
Lemma lt_subterm1 : forall a a'  n'  b', a < a' ->
                                         a < cons a' n' b'.
Proof.
 intros.
 apply lt_trans with (cons a n' b');auto with T1.
 apply head_lt_cons.
Qed.

Lemma lt_subterm2 : forall a a' n n' b b', a < a' ->
                                           nf (cons a n  b) ->
                                           nf (cons a' n' b') ->
                                           b < cons a' n' b'.
Proof.
 intros.
 apply le_lt_trans with (cons a n b).
 right.
 apply tail_lt_cons;auto.
 constructor.
 auto.
Qed.


Hint Resolve nat_lt_cons.
Hint Resolve lt_subterm2 lt_subterm1. 
Hint Resolve T1_size3 T1_size2 T1_size1.


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
 auto.
Qed.


Theorem lt_inc_rpo_0 : forall n, 
                           forall o' o, (T1_size o + T1_size o' <= n)%nat->
                              o < o' -> nf o -> nf o' -> 
                                  rpo (T1_2_term o) (T1_2_term o').
Proof.
 induction n.
 destruct o'.
 inversion 2.
 destruct o.
 simpl.
 inversion 1.
 simpl;inversion 1.
 inversion 2.
 simpl.
 intros; apply Top_gt.
 simpl;trivial.
 inversion 1.
 simpl; intros; apply Top_eq_lex.
 simpl;trivial.
 left.
 apply IHn.
 subst o;subst o'.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (cons a n0 b) + T1_size (cons a' n' b'))%nat.
 simpl;
 auto with arith.
 omega.
 auto.
 auto.
 nf_inv.
 nf_inv.
 simpl;auto.
 inversion_clear 1.
 subst s'.
 change (rpo (T1_2_term a) (T1_2_term (cons a' n' b'))).
 apply IHn;auto.
 subst o;subst o'.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (cons a n0 b) + T1_size (cons a' n' b'))%nat.
 auto with arith.
 auto.
 nf_inv.
 decompose [or] H7.
 subst s'.
 apply nat_lt_cons.
 subst s'.
 change (rpo (T1_2_term b) (T1_2_term (cons a' n' b'))).
 apply IHn;auto.
 subst o;subst o'.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (cons a n0 b) + T1_size (cons a' n' b'))%nat.
 auto with arith.
 auto.
 eauto.
 nf_inv.
 case H8.
 intros.
 simpl;apply Top_eq_lex.
 auto.
 constructor 2.
 constructor 1.
 apply nat_2_term_mono.
 auto.
 auto.
 inversion_clear 1.
 subst s'.
 change (rpo (T1_2_term a) (T1_2_term (cons a n' b'))).
 apply IHn;auto.
 subst o;subst o'.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (cons a n0 b) + T1_size (cons a n' b'))%nat.
 auto with arith.
 auto.
 apply head_lt_cons.
 nf_inv.
 decompose [or] H7.
 subst s'.
 apply nat_lt_cons.
 subst s'.
 change (rpo (T1_2_term b) (T1_2_term (cons a n' b'))).
 apply IHn;auto.
 subst o;subst o'.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (cons a n0 b) + T1_size (cons a n' b'))%nat.
 auto with arith.
 auto.
 apply lt_le_trans with (cons a 0 zero).
 inversion H4.
 auto with T1.
 auto with T1.
 case n'.
 apply le_tail;auto with T1.
 auto with T1 arith.
 nf_inv.
 case H8.
 simpl.
 intros;apply Top_eq_lex.
 auto.
 right.
 right.
 left. 
 apply IHn.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (cons a n0 b) + T1_size (cons a n0 b'))%nat.
 apply plus_lt_compat.
 auto.
 auto.
 subst o;subst o';auto.
 auto.
 nf_inv.
 nf_inv.
 auto.
 inversion_clear 1.
 subst s'.
 eapply Subterm.
 2:eleft.
 left;auto.
 decompose [or] H7.
 subst s'.
 apply nat_lt_cons.
 subst s'.
 change (rpo (T1_2_term b) (T1_2_term (cons a n0 b'))).
 apply IHn.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (cons a n0 b) + T1_size (cons a n0 b'))%nat.
 auto with arith.
 subst o;subst o'.
 auto.
 apply lt_le_trans with (cons a 0 zero).
 inversion H4.
 auto with T1.
 auto with T1.
 case n0.
 apply le_tail;auto with T1.
 auto with T1 arith.
 nf_inv.
 auto.
 case H8.
Qed.
 
Remark R1 : Acc P.prec nat_0. 
 split.
 destruct y; try contradiction.
Qed.

Hint Resolve R1.

Remark R2 : Acc P.prec ord_zero. 
 split.
 destruct y; try contradiction; auto.
Qed.

Hint Resolve R2.

Remark R3 : Acc P.prec nat_S.
 split.
 destruct y; try contradiction;auto.
Qed.


Hint Resolve R3.

Remark R4 : Acc P.prec ord_cons.
 split.
 destruct y; try contradiction;auto.
Qed.

Hint Resolve R4.

Theorem well_founded_rpo : well_founded rpo.
Proof.
 apply wf_rpo.
 red.
 destruct a;auto.
Qed.

Section  well_founded.
 
  Let R := restrict T1 nf lt.

  Hint Unfold restrict R.

 Lemma R_inc_rpo : forall o o', R o o' -> rpo (T1_2_term o) (T1_2_term o').
 Proof.
  intros o o' (H,(H1,H2)).
  eapply lt_inc_rpo_0;auto.
 Qed. 

 
 Lemma nf_Wf : well_founded_P _ nf lt.
Proof.
 unfold well_founded_P.
 intros.
 unfold restrict.
 generalize (Acc_inverse_image _ _ rpo T1_2_term a (well_founded_rpo (T1_2_term a))).
  intro.
 eapply  Acc_incl  with  (fun x y : T1 => rpo (T1_2_term x) (T1_2_term y)). 
 red.
 apply R_inc_rpo.
 auto.
Qed.


End well_founded.


Definition transfinite_induction :
 forall (P:T1 -> Type),
   (forall x:T1, nf x ->
                   (forall y:T1, nf y ->  y < x -> P y) -> P x) ->
    forall a, nf a -> P a.
Proof.
 intros; eapply P_well_founded_induction_type; eauto.
 eexact nf_Wf;auto.
Defined.


Definition transfinite_induction_Q :
  forall (P : T1 -> Type) (Q : T1 -> Prop),
      (forall x:T1, Q x -> nf x ->
           (forall y:T1, Q y -> nf y ->  y < x -> P y) -> P x) ->
   forall a, nf a -> Q a -> P a.
Proof.
 intros.
 eapply P_well_founded_induction_type with (R:=lt)(P:=fun a => nf a /\ Q a).
 3:split;auto.
 2:destruct 1; intros; eapply X; eauto.
 unfold well_founded_P.
 intros.
 apply Acc_incl with (restrict _ nf lt).
 unfold inclusion; intros.
 unfold restrict.
 unfold restrict in H2.
 tauto.
 apply nf_Wf.
 case H1;auto.
Defined.

(* Ordinal arithmetics *)

Fixpoint succ (c:T1) : T1 :=
  match c with zero => finite 1
             | cons zero n _ => cons zero (S n) zero
             | cons a n b => cons a n (succ b)
  end.



Fixpoint pred (c:T1) : option T1 :=
  match c with zero => None
             | cons zero 0 _ => Some zero
             | cons zero (S n) _ => Some (cons zero n zero)
             | cons a n b =>
                  match (pred b) with None => None
                                    | Some c => Some (cons a n c)
                  end
  end.




Fixpoint plus (c1 c2 : T1) {struct c1}:T1 :=
  match c1,c2 with
 |  zero, y  => y
 |  cons zero n _, zero => cons zero n zero
 |  x, zero  => x
 |  cons zero n _, cons zero n' _ => cons zero (S (n+n')) zero
 |  cons a n b, cons a' n' b' =>
      (match compare a a' with
        | Datatypes.Lt => cons a' n' b'
        | Gt => (cons a n (plus b (cons a' n' b')))
        | Datatypes.Eq  => (cons a (S(n+n')) b')
       end)
 end
 where "a + b" := (plus a b) : cantor_scope.


Fixpoint minus (c1 c2 : T1) {struct c1}:T1 :=
  match c1,c2 with
 |  zero, y  => zero
 |  cons zero n _, cons zero n' _ =>
                  if (le_lt_dec n n')
                  then zero
                  else  cons zero (Peano.pred (n-n')) zero
 |  cons zero n _, zero =>  cons zero n zero
 |  cons zero n _, y =>  zero
 |  cons a n b, zero =>  cons a n b
 |  cons a n b, cons a' n' b' =>
      (match compare a a' with
            | Datatypes.Lt => zero
            | Gt => cons a n b
            |  Datatypes.Eq  => (match (lt_eq_lt_dec n n') with
                            | inleft (left _) => zero
                            | inright _ => (cons a (Peano.pred (n-n')) b')
                            | _ =>  b - b'
                      end)

       end)
 end
 where  "c1 - c2" := (minus c1 c2):cantor_scope.

Lemma omega_minus_one : omega - F 1 = omega.
Proof.
 reflexivity.
Qed.



Fixpoint mult (c1 c2 : T1) {struct c2}:T1 :=
  match c1,c2 with
 |  zero, y  => zero
 |  x, zero => zero
 |  cons zero n _, cons zero n' _ =>
                 cons zero (Peano.pred((S n) * (S n'))) zero
 |  cons a n b, cons zero n' b' =>  
                 cons a (Peano.pred((S n) * (S n'))) b
 |  cons a n b, cons a' n' b' =>
     cons (a + a') n' ((cons a n b) * b')
 end
where  "c1 * c2" := (mult c1 c2) : cantor_scope.

Fixpoint exp_F (a:T1)(n:nat){struct n}:T1 :=
 match n with
 | 0 => F 1
 | S p => a * (exp_F a p)
 end.


Fixpoint exp  (a b : T1) {struct b}:T1 :=
  match a,b with
 |  x, zero => cons zero 0 zero
 | cons zero 0 _ , _ => cons zero 0 zero
 | zero, y            => zero
 | x , cons zero n' _ =>  exp_F x (S n')
 | cons zero n _, cons  (cons zero 0 zero) n'  b' =>
        ((cons (cons zero n' zero) 0 zero) *
                ((cons zero n zero) ^  b'))
 | cons zero n _, cons  a' n' b' =>
            (omega_term
                    (omega_term (a' - (F 1)) n')
                    0) *
                 ((cons zero n zero) ^ b')
 | cons a  n b, cons  a' n' b' =>
    ((omega_term   (a * (cons a' n' zero))
                            0) *
            ((cons a n b) ^ b'))
end
where "a ^ b" := (exp a b) : cantor_scope.


(* properties of the data structure *)
(************************************)

(* A tactic for decomposing a non zero ordinal *)
(* use : H : lt zero ?c ; a n b : names to give to the constituents of
   c *)



Definition get_decomposition : forall c, lt zero c ->
                           {a:T1 & {n:nat & {b:T1 | c = cons a n b}}}.
 intro c; case c.
 intro H; elimtype False; inversion H.
 intros c0 n c1; exists c0;exists n;exists c1;auto.
Defined.

Ltac decomp_exhib H a n b e:=
 let Ha := fresh in
 let Hn := fresh in
 let Hb := fresh in
  match type of H
  with lt zero ?c =>
    case (get_decomposition  H);
     intros a Ha;
     case Ha;intros n Hn; case Hn; intros b e;
     clear Ha Hn
  end.



(* characteristic of epsilon0 *)

Lemma lt_a_phi0_a : forall a, a < phi0 a.
Proof.
 induction a;simpl.
 compute; constructor.
 unfold phi0.
 constructor 2.
 assert (le (cons a1 0 zero) (cons a1 n a2)).
 case n.
 case a2.
 left.
 trivial.
 right;constructor 4;constructor.
 right;constructor 3.
 auto with arith.
 case H.
 injection 1.
 intros; subst a2;subst n;auto.
 intro; eapply lt_trans; eauto.  
Qed.



Lemma phi0_lt : forall a b, a < b -> phi0 a < phi0 b.
Proof.
 unfold phi0;intros c c' H.
 constructor 2;trivial.
Qed.


Lemma phi0_ltR : forall a b, phi0 a < phi0 b ->  a < b.
Proof.
 unfold phi0;intros c c' H.
 case (lt_inv H).
 trivial.
 intros [(_,i)|(_,(_,i))]; inversion i.
Qed.






(* Unfortunately, lt is NOT well founded *)




(* compare reflects trichotomy_inf *)

Lemma compare_ok_1:
   forall a a', (compare a a' =  Datatypes.Lt <-> a < a') /\
                (compare a a' =  Datatypes.Eq <-> a = a') .
Proof.
 induction a;simpl.
 destruct a';simpl.
 split;split.
 discriminate 1.
 inversion 1.
 auto.
 auto.
 split;split.
 auto with T1.
 auto.
 discriminate 1.
 discriminate 1.
 destruct a'; simpl.
 split; split.
 discriminate 1.
 inversion 1.
 inversion 1.
 discriminate 1.
 (* use Yves's caseEq *)
 caseEq (compare a1 a'1).
 intros.
 case (lt_eq_lt_dec n n0).
 destruct s.
 repeat split.
 replace a1 with a'1.
 constructor 3;auto.
 case (IHa1 a'1).
 intros.
 case H1;auto.
 intros;symmetry.
 auto.
 discriminate 1.
 injection 1.
 intros;  subst n0.
 absurd (n<n)%nat;auto with arith.
 split.
 repeat split.
 intro.
 subst n0.
 replace a1 with a'1.
 constructor 4.
 case (IHa2 a'2);intros.
 auto.
 case H1;auto.
 elim (IHa1 a'1);intros.
 case H2;auto.
 symmetry;auto.
 subst n0.
 replace a1 with a'1.
 intro.
 assert (lt a2 a'2).
 eapply lt_inv_b;eauto.
 case (IHa2 a'2);intros.
 case H2;auto.
 case (IHa1 a'1);intros.
 case H1;auto.
 intros;symmetry;auto.
 replace a1 with a'1.
 subst n0.
 repeat split.
 intros.
 case (IHa2 a'2); intros.
 replace a2 with a'2.
 auto.
 case H2;intros.
 symmetry;auto.
 injection 1.
 intro;subst a'2.
 case (IHa2 a2).
 intros.
 case H2;auto.
 case (IHa1 a'1);intros.
 case H1;intros;symmetry;auto.
 intro;repeat split.
 discriminate 1.
 intro H0.
 absurd (cons a1 n a2 < cons a'1 n0 a'2);auto.
 apply lt_not_gt.
 replace a1 with a'1.
 constructor 3;auto.
 elim (IHa1 a'1);intros.
 case H2;auto.
 symmetry;auto.
 discriminate 1.
 injection 1.
 intros; subst n0; absurd (n<n)%nat;auto with arith.
 intros; repeat split.
 constructor 2.
 case (IHa1 a'1);intros.
 case H1;auto.
 discriminate 1.
 injection 1;intros.
 subst a'1;absurd (lt a1 a1).
 apply lt_irr.
 case (IHa1 a1);intros.
 case H3;auto.
 intro;repeat split.
 discriminate 1.
 inversion 1.
 case (IHa1 a'1);intros.
 case H8;intros.
 rewrite <- (H11 H2).
 symmetry;auto.
 absurd (cons a'1 n0 a'2 < cons a1 n a2).
 apply lt_not_gt;auto.
 case (IHa1 a'1);intros.
 case H9;intros.
 rewrite H in H11.
 generalize (H11 H5).
 discriminate 1.
 case (IHa1 a'1);intros.
 case H9;intros.
 rewrite H in H11.
 generalize (H11 H5).
 discriminate 1.
 discriminate 1.
 injection 1;intros.
 subst a'1; case (IHa1 a1);intros.
 case H4;intros.
 rewrite H in H6.
 auto.
Qed.



Lemma compare_reflect : forall a a', match compare a a' with
                                    |    Datatypes.Lt => a < a'
                                    |    Datatypes.Eq => a = a'
                                    |    Datatypes.Gt => a' < a
                                    end.
Proof.
 intros c c';  case (compare_ok_1 c c');intros H0 H1; case H0; case H1;
 intros;
   caseEq (compare c c'); auto.
 intro comp; case (trichotomy_inf c c').
 intro x; case x; intro H'.
 rewrite (H4 H') in comp;discriminate comp.
 rewrite (H2 H') in comp;discriminate comp.
 trivial.
Qed.




(* the following theorems were proved in another time and
 place ; It seems that some cleaning is necessary *)

Lemma compare_rw1 : forall a b, a < b -> compare a b =  Datatypes.Lt.
Proof.
 intros c1 c2; generalize (compare_reflect c1 c2).  
 case (compare c1 c2);auto.
 intros e H;subst c2;case (lt_irr H).
 intros H1 H2;case (lt_not_gt H2);auto.
Qed.

Lemma compare_rw2 : forall a, compare a a =  Datatypes.Eq.
Proof.
 intro c; generalize (compare_reflect c c).  
 case (compare c c);auto;
 intro H;case (lt_irr H);auto.
Qed.

Lemma compare_rw3 : forall a b, b < a  -> compare a b = Gt.
Proof.
 intros c1 c2; generalize (compare_reflect c1 c2).  
 case (compare c1 c2);auto.
 intros e H;subst c2;case (lt_irr H).
 intros H1 H2;case (lt_not_gt H2);auto.
Qed.





Theorem compare_reflectR : forall a b : T1,
  (match trichotomy_inf a b with
    inleft  (left _) =>  Datatypes.Lt
  | inleft  (right _) =>  Datatypes.Eq
  | inright _ => Gt
  end)
  = compare a b.
Proof.
 intros c1 c2;case (trichotomy_inf c1 c2).
 destruct s; auto; try discriminate.
 rewrite compare_rw1;auto.
 subst c1;rewrite compare_rw2;auto.
 intro;  rewrite compare_rw3;auto.
Qed.

 

(* on max *)


Lemma max_le_1 : forall a b, a <= max a b.
Proof.
 unfold max.
 intros.
 rewrite <- compare_reflectR.
 case (trichotomy_inf a b);auto with T1.
 destruct s;auto with T1.
Qed.



Lemma max_comm : forall a b, max a b = max b a.
Proof.
 unfold max.
 intros a b; repeat rewrite <- compare_reflectR. 
 case ( trichotomy_inf a b); case (trichotomy_inf b a);auto with T1.
 destruct s; destruct s; auto with T1.
 case (lt_not_gt l);auto.
 destruct s;auto with T1.
 destruct s;auto with T1.
 intros H H0; case (lt_not_gt H);auto.
Qed.




    
Lemma lt_intro : forall a b, compare a b =  Datatypes.Lt -> a < b. 
Proof.
   intros a b; rewrite <- compare_reflectR.
   case (trichotomy_inf a b);auto with T1.
    destruct s; auto.
    discriminate 1.
  discriminate 2.
Qed.



Lemma max_dec : forall a b, {max a b = a}+{max a b = b}.
Proof.
 unfold max;  intros a b; case (trichotomy_inf a b);auto.
 destruct 1.
 repeat rewrite compare_rw1;auto.
 subst b;repeat rewrite compare_rw2;auto.
 intro; repeat rewrite compare_rw3;auto.
Qed.



Lemma max_nf : forall a b, nf a -> nf b -> nf (max a b).
Proof.
 intros c c'; case (max_dec c c');
 intro H;rewrite H;auto.
Qed.



 
Lemma max_assoc : forall a b c, max (max a b) c =
                                max a (max b c).
Proof.
 intros c1 c2 c3.
 unfold max.
 case (trichotomy_inf c1 c2).
 destruct 1.
 repeat (rewrite (compare_rw1 l)).
 
 case (trichotomy_inf c2 c3).
 destruct 1.
 repeat (rewrite (compare_rw1 l0)).
 assert (lt c1 c3).
 eapply lt_trans;eauto.
 rewrite (compare_rw1 H);auto.
 subst c3.
 repeat rewrite compare_rw2.
 rewrite compare_rw1;auto.
 intro c'.
 repeat (rewrite (compare_rw3 c')).
 rewrite compare_rw1;auto.
 subst c2;
 repeat (rewrite (compare_rw2));auto.
 case (trichotomy_inf c1 c3).
 destruct 1.
 repeat (rewrite (compare_rw1 l));auto.
 subst c3;repeat rewrite compare_rw2;auto.
 intro c;repeat (rewrite (compare_rw3 c));auto.
 repeat rewrite compare_rw2;auto.
 intro c; repeat rewrite (compare_rw3 c);auto.
 case (trichotomy_inf c1 c3).
 destruct 1.
 rewrite (compare_rw1 l);auto.
 assert (lt c2 c3).
 eapply lt_trans;eauto.
 repeat rewrite (compare_rw1 H);auto.
 rewrite (compare_rw1 l);auto.
 subst c3;rewrite (compare_rw2);auto.
 repeat rewrite (compare_rw1 c);auto.
 rewrite compare_rw2;auto.
 intro.
 rewrite (compare_rw3 l).
 case (trichotomy_inf c2 c3).
 destruct 1.
 repeat rewrite (compare_rw1 l0);auto.
 repeat rewrite (compare_rw3 l);auto.
 subst c3;repeat rewrite (compare_rw2);auto.
 repeat rewrite (compare_rw3 l);auto.
 intro c';repeat rewrite (compare_rw3 c');auto.
 repeat rewrite (compare_rw3 c);auto.
Qed.


(* Properties of successor *)


Lemma succ_nf2 : forall c a n b, nf2 c (cons a n b) ->
                               nf2 (succ c) (cons a n b).
Proof.
 induction c.
 simpl.
 repeat constructor.
 simpl.
 case c1.
 repeat constructor.
 intros t n0 t0 a n1 b H.
 inversion_clear H.
 constructor; auto.
Qed.

Lemma succ_nf : forall a, nf a -> nf (succ a).
Proof.
 induction a.
 simpl.
 repeat constructor; auto  with arith.
 simpl.
 generalize IHa1 ; case a1.
 simpl;repeat constructor; auto.
 intros c n0 c0 H H0.
 apply nf_intro.
 nf_inv.
 apply IHa2; nf_inv.  
 apply succ_nf2.
 eapply nf2_intro; eauto.
Qed.



(* properties of lt and le *)

Lemma lt_succ :  forall a, a < succ a.
Proof.
  intro c; elim c; simpl; auto with T1.
  intro c0; case  c0; simpl; auto with T1.
Qed.





Lemma phi0_log : forall a, a < phi0 (succ (log a)).
Proof.
 destruct a.
 simpl.
 compute.
 constructor.
 simpl.
 unfold phi0.
 constructor 2.
 apply lt_succ.
Qed.


 

(* properties of addition *)


Lemma plus_zero : forall a, zero + a  = a.
Proof.
 simpl; intro a; case a; auto.
Qed.



Lemma plus_a_zero : forall a, nf a -> a + zero = a.
Proof.
 intro c; case c;simpl.
 trivial.
 intro c0;case c0;simpl;auto.
 intros n c1 H1; rewrite (nf_of_finite H1); auto with T1.
Qed.


Lemma plus_fin_omega : forall n ,F n + omega = omega.
Proof.
 destruct n;simpl;auto.
Qed.


Lemma plus_not_comm : {a:T1 & {b :T1 |
                          nf a /\ nf a /\ a + b  <> b + a}}.
Proof.
 exists (finite 1); exists omega.
 split.
 simpl;repeat constructor.
 split.
 compute;repeat constructor.
 compute.
 discriminate 1.
Defined.


Lemma succ_is_plus_one: forall a, nf a -> succ a = a + F 1.
Proof.
 unfold finite.
 intro c; elim c.
 compute; trivial.
 intro c0;case c0.
 simpl.
 intros H n c1 H0 H1.
 rewrite <- plus_n_O; trivial.
 intros c1 n c2 H n0 c3 H0 H1.
 simpl.
 rewrite H0; [trivial | nf_inv].
Qed.  




(* plus and lt *)

Lemma plus_cons_cons_rw1 : forall a n b a' n' b',
     a < a' ->
     cons a n b + cons a' n' b' = cons a' n' b'.
Proof.
 simpl.
 destruct a.
 destruct a'.
 inversion 1.
 intros; rewrite compare_rw1; auto with T1.
 destruct a'.
 inversion 1.
 intros n' b' H; rewrite (compare_rw1);auto.
Qed.

Lemma plus_cons_cons_rw2 : forall a n b n' b',
      nf (cons a n b) ->
      nf (cons a n' b') ->
      plus (cons a n b) (cons a n' b')=
      cons a (S (n + n') ) b'.  
Proof.
 simpl.
 destruct a.
 intros.
 rewrite (nf_of_finite H0).
 auto.
 rewrite (compare_rw2).
 auto.
Qed.


Lemma plus_cons_cons_rw3 : forall a n b a' n' b',
      a' < a ->
      nf (cons a n b) ->
      nf (cons a' n' b') ->
      cons a n b + cons a' n' b'=
      cons a n (b + (cons a' n' b')).
Proof.
simpl.
destruct a.
inversion 1.

destruct a'.
rewrite compare_rw3.
auto.
constructor.
intros;
rewrite compare_rw3.
auto.
auto.
Qed.


Lemma ap_plus : forall a, ap a ->
    forall b c, nf b -> nf c -> b < a -> c < a -> b + c <  a.
Proof.
 destruct 1.
 intro b; elim b.
 intro c; elim c;intros.
 simpl; auto with T1.
 simpl.
 auto.
 intros c H0.
 intros.
 generalize c0 H2 H4.
 destruct c1.
 rewrite (plus_a_zero).
 auto.
 auto.
 intros.
 case (trichotomy_inf c c1_1).
 destruct 1.
 rewrite (plus_cons_cons_rw1 n t n0 c1_2 l).
 auto.
 subst c1_1.
 (* *)
 rewrite (plus_cons_cons_rw2 H1 H5).
 constructor 2.
 
 inversion H3;auto.
 inversion H8. (* make automatic tactics for that ! *)
 inversion H8.
 intro H7.
 rewrite (plus_cons_cons_rw3).
 constructor 2.
 inversion_clear H3;auto.
 inversion H8.
 inversion H8. (* argh *)
 auto.
 auto.
 auto.
Qed.



Lemma ap_plusR : forall c, nf c -> c <> zero ->
                  (forall a b, nf a -> nf b ->  a < c ->
                          b < c -> a + b < c)  ->
                  ap c.
 destruct c.
 intros; absurd (zero = zero); auto.
 case c2.
 case n.
 constructor.
 intros.
 generalize (H1 (cons c1 0 zero) (cons c1 n0 zero)).
 clear H1;intros.
 assert (nf (cons c1 0 zero)).
 eapply nf_coeff_irrelevance;eauto.
 assert (nf (cons c1 n0 zero)).
 eapply nf_coeff_irrelevance;eauto.
 assert  (lt (cons c1 0 zero) (cons c1 (S n0) zero)).
 constructor 3;auto with arith.  
  assert (lt (cons c1 n0 zero) (cons c1 (S n0) zero) ).
 constructor 3;auto with arith.  
 generalize (H1 H2 H3 H4 H5).
 intro.
 rewrite plus_cons_cons_rw2 in H6.
 simpl in H6.
 case (lt_irr H6).
 auto.
 auto.
 intros.
 assert (nf (cons c1 n zero)).
 constructor.
 nf_inv.
 assert (nf (cons t n0 t0)).
 nf_inv.
 assert (cons c1 n zero < cons c1 n (cons t n0 t0)).
 constructor 4;auto with T1.
 assert (lt (cons t n0 t0)   (cons c1 n (cons t n0 t0))).
 constructor 2.
 inversion H;auto.
 generalize (H1 _ _ H2 H3 H4 H5).
 clear H1 H4 H5;intro.
 rewrite plus_cons_cons_rw3 in H1.
 simpl in H1.  
 case (lt_irr H1).
 inversion H;auto.
 auto.
 auto.
Qed.

Lemma plus_nf0 : forall a, nf a -> forall b c, b < phi0 a ->
                                               c < phi0 a ->
                                               nf b -> nf c ->
                                               nf (b + c).
Proof.
 intros a Ha ; pattern a.
 apply transfinite_induction.
 2:assumption.
 intros x Cx Hx.
 destruct b; destruct c.
 simpl;constructor.
 simpl;auto.
 intros;rewrite plus_a_zero; auto.
 intros.
 case (trichotomy_inf b1 c1).
 destruct 1.
 rewrite plus_cons_cons_rw1.
 auto.
 auto.
 subst c1.
 
 rewrite plus_cons_cons_rw2.
 eapply nf_coeff_irrelevance;eauto.
 auto.
 auto.
 intro; rewrite plus_cons_cons_rw3;auto.
 
 apply nf_intro.
 nf_inv.
 eapply Hx with b1.
 nf_inv.
 inversion_clear H; auto.
 inversion H3.
 inversion H3.
 inversion H1.
 compute;auto with T1.
(* debile *)
 unfold phi0.  
 constructor 2;auto.
 
  unfold phi0.  
 constructor 2;auto.
 nf_inv.
 auto.
 apply nf2_phi0R.
 apply ap_plus.
 unfold phi0;constructor.
 nf_inv.
 auto.
 apply nf2_phi0.
 eapply nf2_intro.
 eauto.
 unfold phi0; constructor 2; auto.
Qed.



Lemma plus_nf : forall a,  nf a -> forall b, nf b -> nf (a + b).
Proof.
 intros.
 case (trichotomy_inf a b).
 destruct 1.
 apply plus_nf0 with b; auto.
 apply lt_trans with b; auto.
 apply lt_a_phi0_a.
 apply lt_a_phi0_a.
 subst b.
  apply plus_nf0 with a; auto.
 apply lt_a_phi0_a.
 apply lt_a_phi0_a.
 intro;  apply plus_nf0 with a; auto.
  apply lt_a_phi0_a.
 apply lt_trans with a.
 auto.
  apply lt_a_phi0_a.
Qed.


Lemma plus_to_cons:  forall a n b,
   nf (cons a n b) -> omega_term a n + b =
                      cons  a n b.
Proof.
simpl.
 destruct a.
 intros n b H.
 rewrite (nf_of_finite H); auto.
 destruct b.
 auto.
 inversion_clear 1.
 case (trichotomy_inf (cons a1 n a2) b1).
 destruct 1.
 absurd (lt b1 b1);eauto with T1.
 eapply lt_trans;eauto.
 subst b1.
 case (lt_irr H0).
 intro; rewrite compare_rw3; auto.
Qed.

Lemma plus_is_zero : forall a b, nf a -> nf b ->
                               a + b  = zero -> a = zero /\
                                                b = zero.
Proof.
 destruct a;destruct b.
 compute.
 auto.
 simpl.
 discriminate 3.
 intro;rewrite plus_a_zero.
 discriminate 2.
 auto.
 simpl.
 case a1;case b1.
 discriminate 3.
 intros c n1 c0 H H0; rewrite compare_rw1.
 discriminate 1.
 constructor.
 intros c n1 c0 H H0; rewrite compare_rw3.
 discriminate 1.
 constructor.
 intros c n1 c0 c3 n2 c4 H H0;
    case (compare  (cons c3 n2 c4) (cons c n1 c0));discriminate 1.
Qed.

Lemma lt_succ_succ : forall a b,
                    a < b -> nf a -> nf b ->
                    succ a < succ b.
Proof.
    induction 1.
    simpl.
    case a.
    constructor 3;auto with arith.
    constructor 2.
    constructor.
    generalize H; simpl.
     case a.
     case a'.
     inversion 1.
     constructor 2.
     constructor 1.
     case a'.
    inversion 1.
    constructor 2;auto.
   simpl.
  case a.
 constructor 3;auto with arith.
 constructor 3;auto.
 simpl.
 case a.
 intros.
 assert (b'=zero).
 inversion H1.
 auto.
 inversion H5.
 subst b';inversion H.
 constructor 4.
 apply IHlt; nf_inv.
Qed.

 
Lemma lt_phi0_phi0 : forall a b, a < b -> phi0 a < phi0 b.
Proof.
 unfold phi0.
 constructor 2.
 auto.
Qed.


      
Lemma le_phi0_phi0 : forall a b, a <= b  -> phi0 a <= phi0 b.
Proof.
 destruct 1.
 subst b;left;auto.
 right;unfold phi0;constructor 2.
 auto.
Qed.


Lemma le_succ_succ : forall a b, nf a -> nf b ->
   a <= b -> succ a <= succ b.
Proof.
 destruct 3.
 subst a;left;auto.
 right.
 apply lt_succ_succ;auto.
Qed.


 
Lemma lt_succ_le_R : forall a,  nf a -> forall b, nf b ->
                      succ a <= b ->  a < b .
 intros c Hc; elim Hc using nf_rect.
 compute.
 intros.
 case H0;intros.
 subst b;auto with T1.
 eapply lt_trans.
 2:eexact H1.
 auto with T1.
 intros.
 inversion_clear H0.
 
 subst b; simpl; auto with T1.
 simpl in H1.
 eapply lt_trans.
 2:eauto.
 auto with T1.
 intros.
 simpl in H5.
 case H5.
 intro; subst b0.
 constructor 4.
 apply lt_succ;auto.
 intro.
 eapply lt_trans.
 2:eauto.
 constructor 4.
 apply lt_succ;auto.
Qed.

Lemma lt_succ_le_2 : forall a,  nf a -> forall b, nf b ->
                      a < succ b ->  a <= b.
 intros c Hc; elim Hc using nf_rect.
 intros;apply zero_le.
 intros.
 generalize H0; case b;simpl.
 intros.
 generalize (lt_inv_nb  H1).
 destruct 1.
 inversion H2.
 case H2;intros.
 inversion H4.
 destruct t.
 
 inversion 1.
 inversion H3.
 assert (n = n0 \/ (n < n0)%nat).
 omega.
 destruct H8.
 rewrite H8.  
 case t.
 left.
 auto.
 right;constructor 4.
 auto with T1.
 right;constructor 3;auto.
 inversion H3.
 right;constructor 2;auto with T1.
 (* ici *)
 destruct b0.
 simpl.
 inversion 2.
 inversion H7.
 simpl.
 case b0_1;simpl.
 inversion 2.
 inversion H7.
 intros.
 inversion_clear H5.
 right;constructor 2;auto.
 right;constructor 3;auto.
 case (H3 b0_2 (nf_inv2 H4) H6).
 intro; subst b';left;auto.
 right;constructor 4;auto.
Qed.




Lemma lt_succ_le : forall a,  nf a -> forall b, nf b ->
                     a < b -> succ a <=  b.
 induction a.
 intros H0 c'; case c'.
 inversion 2.
 destruct t.
 destruct n.
 
 intros.
 inversion_clear H.
 simpl.
 left;auto.
 inversion H2.
 simpl;case n.
 right;constructor 3;auto with arith.
 right; constructor 3;auto with arith.
 simpl;right;constructor 2; auto with T1.
 inversion 3.
 simpl;constructor 2;auto with T1.
 generalize H6;case a1.
 constructor 2;auto with T1.
 constructor 2.
 auto.
 simpl.  
 case a1.
 assert (S n = n' \/ (S n < n')%nat).
 omega.
 case H7.
 intro; subst n'.
 case b'.
 left;auto.
 right;constructor 4;auto with T1.
 right;constructor 3;auto.
 intros.
 right;constructor 3;auto.
 subst b;generalize H0;case a1.
 intro.
 assert (b'=zero).
 inversion_clear H3.
 auto.
 inversion H7.
 subst b'; inversion H6.
 simpl.
 intros.
 case (IHa2 (nf_inv2 H) b').
 eapply nf_inv2;eauto.
 auto.
 destruct 1;left;auto.
 intro;apply le_tail.
 right;auto.
Qed.



(* About minus *)

Lemma minus_lt : forall a b, a < b -> a - b = zero.
 induction 1;simpl.
 auto.
 generalize H;case a.
 case a';simpl;auto.
 intro H0;case (lt_irr H0).
 intros.
 rewrite (compare_rw1  H0).
 auto.
 case a.
 case (le_lt_dec n n').
 auto.
 intro H0; absurd (n < n)%nat;auto with arith.
 eauto with arith.
 intros;rewrite (compare_rw2).
 case (lt_eq_lt_dec n n').
 destruct s.
 auto.
 subst n';absurd (n < n)%nat;auto with arith.
 intro; absurd (n<n)%nat;eauto with arith.
 case a.
 case (le_lt_dec n n).
 auto.
 intro; absurd (n>n);auto with arith.
 intros; rewrite (compare_rw2).
 case (lt_eq_lt_dec n n).
 destruct s.
 auto.
 auto.
 intro; absurd (n < n)%nat;auto with arith.
Qed.



Lemma minus_a_a : forall a, a - a = zero.
Proof.
 induction a;simpl;auto.
 case a1.
 case (le_lt_dec n n).
 auto.
 intros; absurd (n < n)%nat; auto with arith.
 case (lt_eq_lt_dec n n ).
 destruct s.
 absurd (n < n)%nat;auto with arith.
 intros;rewrite compare_rw2.
 rewrite IHa2;auto.
 intro; absurd (n<n)%nat;auto with arith.
Qed.
 
 
Lemma minus_le : forall a b, a <= b -> a - b = zero.
Proof.
 destruct 1.
 subst b; apply minus_a_a.
 apply minus_lt;auto.
Qed.

Lemma mult_fin_omega : forall n,
                          (F (S n)) * omega = omega.
Proof.
 simpl.
 unfold omega;auto.
Qed.




Lemma phi0_plus_mult : forall a b, nf a -> nf b ->
                       phi0 (a + b) = phi0 a * phi0 b.
Proof.
 simpl.
 intro a; case a.
 intro b; case b;simpl.
 compute;trivial.
 compute; trivial.
 intros until b;case b;simpl.
 case t;simpl;auto.
 intro H; rewrite (nf_of_finite H).
 compute;trivial.
 case t;simpl.
 compute;auto.
 unfold phi0;auto.
Qed.

(** operations on T1 extend operations on nat *)

Lemma succ_compat : forall n:nat, succ (F n) = F (S n).
Proof.
 destruct n;  compute ; trivial.
Qed.


Lemma plus_compat: forall n p, F n + F p = F (n + p)%nat.
Proof.
 induction  n; destruct p; simpl ; auto.
 rewrite <- (plus_n_O n);auto.
 rewrite plus_n_Sm;auto.
Qed.


Lemma mult_compat : forall n p,  (F n) * (F p) =
                                  F (n * p)%nat.
Proof.
 induction n; destruct p; simpl; auto.
 rewrite (mult_0_r n).
 (*  pb of theorem name : mult_0_r versus mult_n_O. *)
 compute; trivial.
Qed.


Lemma exp_F_compat :
 forall p n, exp_F (F n) p =
             F (n ^ p)%nat.
Proof.
 induction p;simpl.
 trivial.
 intro n.
 rewrite (IHp n).
 rewrite mult_compat; trivial.
Qed.

(* the following proof is too? long *)

Lemma exp_compat : forall p n, (F n) ^ (F p) =
                                    F (n ^  p)%nat.
Proof.
 induction p.
 destruct n;simpl.
 auto.
 destruct n;auto.
 destruct n;simpl.
 auto.
 case n.
 simpl.
 rewrite power_of_1.
 rewrite <- plus_n_O;auto.
 
 simpl.
 intros.
 replace (cons zero (S n0) zero) with (finite (S (S n0))).
 2:simpl;auto.
 rewrite exp_F_compat.
 rewrite mult_compat.
 assert ( (S (S n0) * S (S n0) ^ p) =
    (S (S n0) ^ p + (S (S n0) ^ p + n0 * S (S n0) ^ p)))%nat.
 ring.
 rewrite H;trivial.
Qed.



Lemma mult_0_a : forall a, zero * a  = zero.
Proof.
 induction a;simpl;auto.
Qed.

Lemma mult_a_0 : forall a, a * zero = zero.
Proof.
 simple induction a; simpl.
 auto.
 destruct t;auto.
Qed.


Lemma mult_1_a : forall a, nf a -> (F 1) * a = a.
 induction a.
 simpl.
 trivial.
 simpl.
 
 simpl in IHa2.
 intro.
 caseEq a1.
 intro.
 subst a1.
 rewrite (nf_of_finite H).
 rewrite <- (plus_n_O n).
 auto.
 intros.
 subst a1.
 unfold finite in IHa2.
 rewrite IHa2.
 auto.
 nf_inv.
Qed.


 Lemma mult_a_1 : forall a, nf a -> a *  (F 1)  = a.
 induction a.
 simpl.
 trivial.
 simpl.
 
 simpl in IHa2.
 intro.
 caseEq a1.
 intro.
 subst a1.
 rewrite mult_1_r.
 rewrite (nf_of_finite H).
 auto.
 intros.
 subst a1.
  rewrite mult_1_r;auto.
Qed.

Lemma exp_fin_omega : forall n, (F (S (S n)))^ omega = omega.
Proof.
 reflexivity.
Qed.

Lemma omega_exp_rw : forall a, nf a -> omega ^ a =  phi0 a.
Proof.
 unfold omega, phi0;simpl.
 intro a; elim a; simpl.
 trivial.
 destruct t.
 simpl.
 intros.
 generalize (nf_of_finite H1).
 intro; subst t.
 case n;simpl.
 auto.
 simpl.
 induction n0;simpl.
 auto.
 rewrite IHn0.
 simpl.
 auto.
 intros.
 unfold omega_term.
 rewrite H0.
 fold (phi0 t).
 fold (phi0 (cons (cons t1 n t2) n0 t)).
 fold (phi0 (cons (cons t1 n t2) n0 zero)).
 rewrite <- (plus_to_cons H1).
 rewrite  phi0_plus_mult.
 unfold omega_term;auto.
 unfold omega_term;constructor.
 nf_inv.
 nf_inv.
 nf_inv.
Qed.



Lemma omega_term_ambiguity : forall a n, nf a -> omega_term a n =
                                                 (omega ^ a) * (F (S n)).
 Proof.
  intros a n H; rewrite omega_exp_rw.
  simpl.
 case a; simpl; unfold omega_term; auto.
 rewrite <- (plus_n_O n).
 auto.
  rewrite <- (plus_n_O n).
 auto.
 auto.
Qed.

Lemma cons_ambiguity : forall a n b, nf(cons a n b) ->
                       cons a n b = (omega^a)*(F (S n))+b.
Proof.
 intros.
 rewrite <- plus_to_cons.
 rewrite omega_term_ambiguity; auto.
 nf_inv.
 auto.
Qed.

Lemma cons_unicity : forall a n b a' n' b',
                    nf (cons a n b) -> nf (cons a' n' b') ->
                    (omega^a)*(F (S n))+b = (omega^a')*(F (S n'))+b' ->
                    a=a' /\ n = n' /\ b = b'.
Proof.
 intros a n b a' n' b' N N'.
 rewrite <- (cons_ambiguity N).
 rewrite <- (cons_ambiguity N').
 injection 1;auto.
Qed.

 
Theorem Cantor_normal_form :
  forall o, zero < o -> nf o ->
    {a:T1 & {n: nat &{b : T1 | o = omega ^ a * (F (S n)) + b  /\
                               nf (cons a n b) /\
                    (forall a' n' b', nf (cons a' n' b') ->
                      o = omega ^ a' * (F (S n')) + b' ->
                     a = a' /\ n=n' /\ b = b' )}}}.
Proof.
 intro ; case o.
 intro i; case (lt_irr i).
 intros a n b H H0.
 exists a;exists n;exists b; split.
 apply cons_ambiguity;auto.
 split;[auto|intros a' n' b' H' e'].
 apply cons_unicity;auto.
 rewrite <- e'.
 symmetry;apply cons_ambiguity;auto.
Defined.


Lemma trichotomy : forall a b, a < b \/ a = b \/ b < a.
Proof.
 intros a b; case (trichotomy_inf a b); auto.
 destruct 1;auto.
Qed.

Ltac tricho t t' Hname := case (trichotomy t t');
                           [auto with T1 | 
                            auto with T1 | 
                            intro Hname |
                            intros [Hname|Hname]].




