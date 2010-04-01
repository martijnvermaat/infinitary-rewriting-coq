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

Require Import More_nat.
Require Import EPSILON0.

(* we still not use Standard Library's multisets : should we ? *)


Inductive nfs : T1 -> Prop := 
|nfs_nil :  nfs zero
|nfs_cons :  forall a n b,  nf a -> nfs b -> nfs (cons a n b).


Hint Constructors nfs nf : T1.


Lemma nf_nfs : forall a, nf a -> nfs a.
Proof.
 induction 1; simpl; auto with T1.
Qed.


(*  Number of occurrences of c in a *)

Fixpoint multiplicity (c:T1) (a:T1) {struct a}: nat :=
  match a with
  | zero => 0
  | (cons a' n' b') =>
      match T1_eq_dec c a' with
      | left _ => ( (S n') +(multiplicity c b'))%nat
      | right _ => multiplicity c b'
      end
  end.

Lemma multiplicity_rw1 : forall a  n b, multiplicity a (cons a n b) = 
                                  (S n + multiplicity a b)%nat.
  simpl.
 intros; case (T1_eq_dec a a). 
 auto.
 intro; absurd (a=a);auto.
Qed.

Lemma multiplicity_rw2 : forall a  a' n' b', a <> a' ->
                         multiplicity a (cons a' n' b') = multiplicity a b'.
Proof.
 simpl.
 intros; case (T1_eq_dec a a'). 
 intro; case H;auto.
 auto.
Qed.

Fixpoint app (o o':T1) {struct o} : T1 :=
  match o with zero => o'
             | cons a n b => cons a n (app b  o')
  end.

Infix "::" := app (at level 60, right associativity) : cantor_scope.


Lemma multiplicity_of_app : forall l l' a, multiplicity a (l ::  l') =
                                     (multiplicity a l + multiplicity a l')%nat.
Proof.
 induction l; simpl; auto with arith.
 intros.
 case (T1_eq_dec a l1).
 rewrite IHl2.
 clear IHl1 IHl2; intro; omega.
 auto.
Qed.



Definition equiv (l l':T1) := 
    forall o, multiplicity o l = multiplicity o l'.


(* equiv is an equivalence ! *)

Lemma equiv_refl : forall l:T1, equiv l l.
Proof.
 unfold equiv; trivial.
Qed.

Lemma equiv_sym : forall l l':T1, equiv l l' -> equiv l' l.
Proof.
  unfold equiv; auto.
Qed.

Lemma equiv_trans :
 forall l l' l'', equiv l l' -> 
                         equiv l' l'' -> 
                         equiv l l''.
Proof.
 intros l l' l'' H H0 z.
 eapply trans_eq; eauto.
Qed.


Lemma equiv_cons :
 forall a n l l', equiv l l' -> 
                  equiv (cons a n l) (cons a n l').
Proof.
 intros a n l l' H a'.
 simpl ; case (T1_eq_dec a' a); auto. 
Qed.

Lemma equiv_tail : forall a n  l l', equiv (cons a n l) (cons a n l') -> 
                                     equiv l l'.
Proof.
 intros.
 unfold equiv;intros.
 generalize (H o).
 simpl.
 case (T1_eq_dec o a).
 intro;omega.
 auto.
Qed.


Lemma equiv_perm :
 forall a n b p l l',
   equiv l l' -> 
   equiv (cons a n (cons b p l))(cons b p (cons a n l')).
Proof.
 intros a n b p l l' H c; simpl.
 case (T1_eq_dec c a); case (T1_eq_dec c b); 
  simpl; case (H c); auto.
 intros;ring.
Qed.

Lemma app_equiv_comm : forall l l', equiv (l :: l') (l' :: l).
 unfold equiv;intros.
 do 2 rewrite multiplicity_of_app.
 auto with arith.
Qed.


Lemma app_equiv_assoc : forall l l' l'', equiv ((l ::l') :: l'') 
                                           (l :: (l' :: l'')).
 unfold equiv;intros.
 repeat rewrite multiplicity_of_app.
  auto with arith.
Qed.

 
Lemma equiv_cong1 : forall l1 l2 l, equiv l1 l2 -> equiv (l1 :: l) 
                                                         (l2 :: l).

 unfold equiv;intros;repeat rewrite multiplicity_of_app.
 auto with arith.
Qed.


 Lemma equiv_cong2 : forall l1 l2 l, equiv l1 l2 -> equiv (l :: l1) 
                                                          (l :: l2).

 unfold equiv;intros;repeat rewrite multiplicity_of_app.
 auto with arith.
Qed.



Hint Resolve equiv_cons equiv_refl equiv_perm equiv_tail app_equiv_assoc : T1.



(* insertion of z into l at the right place 
   (assuming l is sorted) 
*)

Fixpoint sort_aux (a:T1)(n:nat) (l:T1) {struct l} : T1 :=
  match l with
  | zero => (cons a n zero)
 |  cons b p l' =>
     ( match trichotomy_inf a b with
      |  inleft (left _ ) =>  (cons b p (sort_aux a n l'))
      | inleft (right _) => (cons b (S  n +p)%nat  l')
      | inright _ => (cons a n (cons b p l'))
      end)
   end.




(* the sort_aux function seems to be a good tool for sorting ... *)

Lemma sort_aux_equiv : forall l a n, 
                  equiv (cons a n l) (sort_aux a n l).
Proof.
 induction l ; auto with T1.
 intros x n0; simpl. case (trichotomy_inf x l1).
 
 destruct s.
 eapply equiv_trans.
 2:eapply equiv_cons.
 apply equiv_perm.
 apply equiv_refl.
 auto.
 subst l1.
 2:intro;apply equiv_refl.
 unfold equiv;simpl.
 intro o;case (T1_eq_dec o x).
 intro; omega.
 auto.
Qed.


(* ici *)


Lemma sort_aux_nf :
 forall (l x:T1) n,  nf x -> nf l -> nf (sort_aux x n l).
Proof.
 induction 2.

 simpl.
 auto with T1.

 simpl.
 case (trichotomy_inf x a).
 destruct s.
 constructor;auto.
 constructor; auto with T1.
 constructor; auto with T1 arith.
  constructor; auto with T1 arith.
 simpl.
case (trichotomy_inf x a).
destruct s.
simpl in IHnf2.
generalize IHnf2. 
case (trichotomy_inf x a').
destruct s.
constructor 3. 
 auto. 
 auto.
auto.

subst x. 
 constructor;auto.
 constructor;auto.
 constructor;auto.
constructor.
auto.
auto.
 constructor;auto.
Qed.


(* the sorting function *)
(* supprimer la prÃ©conditions nfs l *)

Fixpoint sort (alpha :T1) : T1 :=
 match alpha with zero => zero
            | cons a n b => sort_aux a n (sort b)
 end.

Lemma sort_equiv :
  forall alpha:T1, equiv alpha (sort alpha).
Proof.
 induction alpha;simpl.
 split;auto with T1.
 apply equiv_trans with (cons alpha1 n (sort alpha2)).
 apply equiv_cons.
 auto.
 apply sort_aux_equiv.
Qed.

Lemma sort_nf : forall alpha, nfs alpha -> nf (sort alpha).
Proof.
 induction alpha;simpl.
 constructor.
 intro; apply sort_aux_nf.
 inversion H;auto.
 apply IHalpha2.
 inversion H;auto.
Qed.


(* something to do with multisets ? *)



Definition ltM (a:T1)(l l':T1) :=
 (multiplicity a l < multiplicity a l')%nat /\
 forall b,  a < b -> multiplicity b l = multiplicity b l'.


Lemma ltM_equiv_ltM : forall a l l' l'', ltM a l l' -> 
                                         equiv l' l'' -> ltM a l l''.
Proof.
 unfold ltM, equiv.
 intros.
 case H; intros; clear H.
 split. 
 rewrite <- H0; auto.
 intros; rewrite <- H0;auto.
Qed.

Lemma ltM_equiv_ltMR : 
  forall a l l' l'', ltM a l l' -> equiv l l'' -> ltM a l'' l'.
Proof.
 unfold ltM, equiv.
 intros.
 case H; intros; clear H.

 split. 
 
 rewrite <- H0; auto.
 intros; rewrite <- H0;auto.
Qed.


(* never used *)
Lemma ltM_trans : forall a l l' , ltM a l l' -> forall l'', ltM a l' l'' ->
                                                            ltM a l l''.
 induction 1.
 destruct 1.
 split.
 eauto with arith.
 intros ; rewrite H0; auto.
 Qed.

(* never used *)

Lemma ltM_trans_1 : forall a b l l' l'', a < b -> ltM a l l' -> 
                                          ltM b l' l'' ->
                                          ltM b l l''.
 destruct 2.
 destruct 1.
 split.
 replace (multiplicity b l) with (multiplicity b l').
 auto.
 symmetry;apply H1; auto.
 intros; transitivity (multiplicity b0 l');auto.
 apply H1.
 eapply lt_trans; eauto.
Qed.

Lemma ltM_trans_2 : forall a b l l' l'',  b <  a -> ltM a l l' -> 
                                          ltM b l' l'' ->
                                          ltM a l l''.
 destruct 2.
 destruct 1.
 split.
 replace (multiplicity a l'') with (multiplicity a l').
 auto.
 apply H3.
 auto.
 intros;
 transitivity (multiplicity b0 l');auto.
 apply H3.
 eapply lt_trans; eauto.
Qed.

 (* should be interesting to consider a projection 
    exists a, ltM a l l' 
 *)


 Lemma lt_ltM : forall a n b l l',  b < a -> ltM a l l' -> 
                                     ltM a (cons b n l) l'.
 induction 2; split.
 simpl.
 case (T1_eq_dec a b).
 intro; absurd (lt a a);auto with T1.
 subst b;auto.
 auto.
 intros; simpl.
 case (T1_eq_dec b0 b).
 intro; subst b0; case (lt_not_gt H);auto.
 auto.
 Qed.


(* proof too much long ! *)

Lemma nf_multiplicity_head : forall l c n , nf (cons c n l) ->
                                          multiplicity c (cons c n l) = S n.
Proof.
 induction l.
 simpl.
 intros; case (T1_eq_dec c c).
 auto with arith.
 intros; absurd (c=c); auto. 
 intros;case (T1_eq_dec c c).
 2: intros;absurd (c=c);auto.
 case (T1_eq_dec c l1); simpl.
 assert (c <> l1).
 red; intro; subst l1.
 case (lt_irr (a:=c)).
 inversion_clear H;auto.
 intros; absurd (c=l1);auto.
 assert (nf (cons c n0 l2)).
 generalize H;induction l2.
 constructor.
 inversion H;auto.
 constructor.
 inversion H;auto.
 apply lt_trans with l1;auto.
 inversion H8;auto.
 inversion H0;auto.
 inversion H0.
 inversion H8;auto.
 intros; case (T1_eq_dec c c).
 case (T1_eq_dec c l1).
 intro;case n1;auto.
 replace (multiplicity c l2) with 0. 
 auto with arith.
 generalize H0;elim l2.
 simpl;auto.
 intros.
 simpl.
 case (T1_eq_dec c t).
 intro.
 subst t; inversion H3.
 case (lt_irr H7).
 intro;apply H2.
 generalize H3;case t0.
 constructor;auto.
 inversion H3;auto.
 constructor;auto.
 inversion H4.
 apply lt_trans with t;auto.
 inversion H12;auto.
 inversion H4;auto.
 inversion H4.
 inversion H12;auto.
 intro H1;case H1;auto.
Qed.


(* Should make the previous proof simpler  *)

Lemma nf_multiplicity_tail : forall l a c n , 
                                 a < c -> nf (cons c n l) ->
                                 multiplicity a (cons c n l) = multiplicity a l.
Proof.
 inversion_clear 2.
 simpl;case (trichotomy_inf a c).
 destruct 1.
 case (T1_eq_dec a c).
 intro; subst a; absurd (lt c c);auto with T1.
 auto.
 case (T1_eq_dec a c).
 intro; subst a; absurd (lt c c);auto with T1.
 auto .
 
 case (T1_eq_dec a c).
   intro; subst a; absurd (lt c c);auto with T1.
 auto.
 simpl.
  case (T1_eq_dec a c).
 case (T1_eq_dec a a').
   intro; subst a; intros;absurd (lt c c);auto with T1.
 subst c;auto.
  intros; subst a; intros;absurd (lt c c);auto with T1.
  auto.
Qed.



Lemma  nf_multiplicity_big : forall l a c n , c < a -> nf (cons c n l) ->
                                                 multiplicity a (cons c n l) = 0.

Proof.
 induction l.
 inversion_clear 2.
 simpl; case (T1_eq_dec a c).
 intros; subst a; intros;absurd (lt c c);auto with T1.
 auto.
 simpl.
 intros.
 case (T1_eq_dec a c).
 intros; subst a; intros;absurd (lt c c);auto with T1. 
 intro;
 case (T1_eq_dec a c).
 intro; subst a.
 case (lt_irr  H);auto.
intros; case (T1_eq_dec a l1).
intro; absurd (lt a l1).
rewrite <- e.
subst l1.
apply lt_irr.
subst l1.
inversion_clear H0;auto.
eapply lt_trans;eauto.
generalize (IHl2 a c n H).
simpl.
case (T1_eq_dec a c).
intro; absurd (a=c);auto.
intros.
apply H1.
inversion_clear H0.
auto.
inversion_clear H4.
constructor;auto.
constructor; auto.
eapply lt_trans ; eauto.
Qed.




Lemma ltM_inv : forall a b n l l', 
  nf (cons b n l) ->  nf  (cons b n l') ->
  ltM a (cons b n l) (cons b n l') ->
                    ltM a l l'.
Proof.
 inversion_clear 3.
 case (trichotomy_inf a b).
 destruct 1.
 do 2 rewrite nf_multiplicity_tail in H2; auto.
 split;auto.
 intros.
 generalize (H3 _ H1).
 simpl.
 case (T1_eq_dec b0 b).
 auto.
 clear H3;intro;omega.
 auto.
 subst b; do 2 rewrite nf_multiplicity_head in H2;auto.
 absurd (n<n)%nat; auto with arith.
 intro.
 do 2 rewrite nf_multiplicity_big in H2;auto.
 inversion H2.
Qed.



Lemma ltM_inv2 : forall l l' a b n b' n',  nf (cons b n l) ->
                                       nf (cons b' n' l') ->
                                       ltM  a (cons b n l) (cons b' n' l') ->
                                         a <= b'.
intros.
case H1.
intros H2 H3.
case (trichotomy_inf a b').
destruct 1.
auto.
auto.
right;auto.
left;auto.
intro.
rewrite (nf_multiplicity_big  _ _ _ _ l0 H0) in H2;auto.
inversion H2.
Qed.




Lemma ltM_inv3: forall l l' a b n b' n',  a < b' -> 
                                         nf (cons b n l) ->
                                         nf (cons b' n' l') ->
                                         ltM  a (cons b n l) (cons b' n' l') ->
                                          b = b' /\ n = n'.
intros.
case H2.
intros.
case (trichotomy_inf b b').
destruct 1.
generalize (H4 _ H).
rewrite nf_multiplicity_big;auto.
rewrite nf_multiplicity_head.
discriminate 1.
auto.
split.
auto.
subst b'.
generalize (H4 _ H).
rewrite nf_multiplicity_head ;auto.
rewrite nf_multiplicity_head ;auto.
intro.
assert (lt a b).
eapply lt_trans;eauto.
generalize (H4 _ H5).
rewrite nf_multiplicity_head ;auto.
rewrite nf_multiplicity_big ;auto.
intro;absurd (0<n)%nat.
discriminate H6.
discriminate H6.
Qed.


Lemma ltM_cons : forall a l l' b n, ltM a l l' -> ltM a (cons b n l)
                                                         (cons b n l').
Proof.
 intros.
 unfold ltM.
 case H; intros.
 split; simpl.
 case (T1_eq_dec a b).
 auto with arith.
 auto.
 intros; case (T1_eq_dec b0 b).
 intro; subst b0;auto.
 intro;apply H1.
auto.
Qed.

Lemma ltM_app : forall a l l' l'', ltM a l l' -> ltM a (l'' :: l)
                                                       (l'' :: l').
Proof.
 induction l'';simpl.
 auto.
 intros;apply ltM_cons.
 auto.
Qed.



Lemma ltM_appR : forall a l l' l'', ltM a l l' -> ltM a (app l l'')
                                                        (app l' l'').
Proof.
  intros.
  eapply ltM_equiv_ltM.
  2:apply app_equiv_comm.
  eapply ltM_equiv_ltMR.
  2:apply app_equiv_comm.
 apply ltM_app.
 auto.
Qed.



Lemma lt_ltM2 : forall c c', nf c -> nf c' ->
                             c < c' -> 
                            {a:T1| ltM a c c'}.
Proof.
 induction c; destruct c'.
 intros; elimtype False.
 inversion H1.
 exists c'1;simpl.
 constructor.
 simpl.
 case (T1_eq_dec c'1 c'1).
 auto with arith.
 intros; absurd (c'1=c'1);auto.
 intros;rewrite nf_multiplicity_big.
 simpl;auto.
 auto.
 auto.
 intros;elimtype False.
inversion H1.
intros.
case (trichotomy_inf c1 c'1).
destruct 1.

exists c'1.
simpl.
inversion H1.
split.


rewrite nf_multiplicity_big.
rewrite nf_multiplicity_head.
auto with arith.
 auto.
 auto.
 auto.
intros; repeat rewrite nf_multiplicity_big.
auto.
auto.
auto.
eapply lt_trans;eauto.
 auto.
 split.
 repeat rewrite nf_multiplicity_head.
 auto with arith.
 auto.
 subst c'1.
 auto.
intros.

repeat rewrite nf_multiplicity_big;auto.
subst c'1;auto.
subst c'1; case (lt_irr l).
subst c'1.

case (lt_eq_lt_dec n n0).
destruct 1.
exists c1.
split.
repeat rewrite nf_multiplicity_head.
auto with arith.
auto.
auto.
intros; repeat rewrite nf_multiplicity_big;auto.
subst n0.
assert (lt c2 c'2).
eapply lt_inv_b;eauto.

case (IHc2 c'2).
eapply nf_inv2;eauto.

eapply nf_inv2;eauto.
auto.
intros;exists x.
apply ltM_cons.
auto.
intros.
elimtype False.
 generalize (lt_inv_nb H1).
destruct 1.
absurd (n<n)%nat;eauto with arith.
case H2;intros ;subst n.
absurd (n0<n0)%nat;auto with arith.
intros.
absurd (EPSILON0.le c1 c'1).
unfold EPSILON0.le.
red; destruct 1.
subst c'1;case (lt_irr l).
case (lt_not_gt l);auto.
inversion H1.
right;auto.
subst c1;left;auto.
left.
auto.
Qed.



(* to do : use natural_sigma and forget about being sorted *)

Lemma ltM_lt : forall a l l', nf l -> nf l' -> 
                          ltM a l l' ->
                          l < l'.
Proof.
 induction l; destruct l'.
 intros; absurd (ltM a zero zero);auto.
 unfold ltM;simpl.
 red; case 1.
 destruct 2.
 inversion H2.
 simpl.
 auto with T1.
 inversion 3.
 inversion H2.
 intros.
 case (trichotomy_inf l1 l'1).
 destruct 1.
 constructor 2;auto.
 subst l'1.
 case (trichotomy_inf a l1).
 destruct 1.
 case H1;intros.
 rewrite  (nf_multiplicity_tail _ _ _ _ l H) in H2.
 rewrite  (nf_multiplicity_tail _ _ _ _ l H0) in H2.
 generalize (H3 _ l).
 rewrite nf_multiplicity_head .
 rewrite nf_multiplicity_head .
 injection 1.
 intro; subst n0.
 constructor 4.
 apply IHl2.
 inversion_clear H; eauto.
 constructor.
 inversion_clear H0; eauto.
 constructor.
 split.
 auto.
 intros b H11.
 generalize (H3 _ H11).
 simpl.
 case (T1_eq_dec b l1).
 intros; clear H3; omega.
 auto.
 auto.
 auto.
 subst l1.
 case H1;intros.
 do 2 rewrite nf_multiplicity_head in H2.
 constructor 3;auto.
 clear H3;omega.
 auto.
 auto.
 auto.
 case H1;intros.
 do 2 rewrite nf_multiplicity_big in H2.
 inversion_clear H2.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 auto.
 intro.
 generalize (ltM_inv2 _ _ _ _ _ _ _ H H0 H1).
 destruct 1.
 subst l'1.
 case H1;intros.
 generalize (H3 _ l).
 rewrite (nf_multiplicity_head);auto.
 rewrite (nf_multiplicity_big);auto.
 intro.
 discriminate H4.
 generalize (ltM_inv3 _ _ _ _ _ _   _ H2 H H0  H1).
 destruct 1.
 subst l'1.
 case (lt_irr l).
Qed.

 
Lemma ltM_tail : forall a n l,  ltM a l (cons a n  l).
Proof.
 intros; unfold ltM.
 split.
 simpl.
 case (T1_eq_dec a a).
 intro; omega.
 intro; absurd (a=a);auto.
 intros; simpl.
 case (T1_eq_dec b a).
 intro; absurd (lt a b).
subst b;auto with T1.
 auto.
 auto.
Qed.

Lemma ltM_head : forall a n a' p l , a' < a -> 
                                     ltM a (cons a' p l)
                                           (cons a n l).
Proof.
 intros; unfold ltM.
 split.
 simpl.
 case (T1_eq_dec a a').
 intro.
 absurd (lt a a);auto with T1.
 subst a;auto.
 case (T1_eq_dec a a).
 intros;omega.
 intros; absurd (a=a);auto.
 simpl.
 intros;case (T1_eq_dec b a'); case (T1_eq_dec b a).
 intro; subst b; absurd (lt a a);auto with T1.
 intros.
 subst b; case (lt_not_gt H0);auto.
 intro; subst b; absurd (lt a a);auto with T1.
 auto.
Qed.


Lemma nfs_to_nf : forall l a, nfs l -> (0 < multiplicity a l)%nat -> nf a.
Proof.
  induction l.  
  simpl.
  inversion 2.
  simpl.
  intros; case (T1_eq_dec a l1).
  intro; subst a.
  inversion H;auto.
  generalize H0; case (T1_eq_dec a l1).
  intros; absurd (a=l1);auto.
  intros.
  apply IHl2.
  inversion H.
  auto.
  auto.
 Qed.


Lemma nf_to_nfs : forall l, nf l -> 
                       nfs l.
Proof.
  induction l.
  constructor.
  constructor.
  inversion H;auto.
  inversion H;auto.
  constructor.
  subst l2.
  auto.
 Qed.


Lemma nf_unicity :forall l, nf l -> forall l',equiv l l' -> nf l' -> l=l'.
Proof.
 induction 1.
 induction 2.
 auto.
 unfold equiv in H.
 generalize (H a).
 simpl.
 case (T1_eq_dec a a).
 discriminate 2.
 intros; absurd (a=a);auto.
 unfold equiv in H.
 generalize (H a).
  simpl.
  case (T1_eq_dec a a).
  discriminate 2.
 intros; absurd (a=a);auto.
 destruct l'.
  unfold equiv .
 intro H0;generalize (H0 a).
 simpl.
 case (T1_eq_dec a a).
 discriminate 2.
  intros; absurd (a=a);auto.
 case l'2.
 unfold equiv; simpl.
 intros.  
  generalize (H0 a).
 case (T1_eq_dec a a).
 case (T1_eq_dec a l'1).
 intros.
 subst l'1.
 assert (n=n0).
 clear H0;omega.
 subst n;auto.
 discriminate 3.
 intro; absurd (a=a);auto.
 unfold equiv. 
 intros.
 generalize (H0 l'1).
 simpl.
 case (T1_eq_dec l'1 a).
 intro;subst l'1.
 case (T1_eq_dec a a).
 case (T1_eq_dec a t).
 intros;subst t.
 absurd (lt a a).
 apply lt_irr.
  inversion_clear H1;auto.
 intros.
 generalize (H0 t).
 simpl.
 case (T1_eq_dec t a).
 intro; absurd (t = a);auto.
case (T1_eq_dec t t).
 discriminate 3.
 
 intro; absurd (t=t);auto.
 intro;absurd (a=a);auto.
 case (T1_eq_dec l'1 l'1).
 discriminate 3.
 intro;absurd (l'1 = l'1);auto.
 destruct l'. 
 unfold equiv.
 intros.
 generalize (H2 a);simpl.
 case (T1_eq_dec a a).
 discriminate 2.
 intro;absurd (a=a);auto.
 case l'2.
 unfold equiv;intros .
 generalize (H2 a).
 simpl.
 case (T1_eq_dec a a).
 case (T1_eq_dec a a').
 intros;subst a'.
 case (lt_irr H).
 case (T1_eq_dec a l'1).
 intro; subst l'1.
 
 generalize (H2 a').
 simpl.
 case (T1_eq_dec a' a).
 intro; absurd (a'=a);auto.
 subst a'.
 case (lt_irr H).
 case (T1_eq_dec a' a').
 discriminate 3.
 
 intro;absurd (a'=a');auto.
 
 discriminate 4.
 intro;absurd (a=a);auto.
 intros.
 case (trichotomy_inf  a l'1).
 destruct 1.
 unfold equiv in H2.
 generalize (H2 l'1).
 rewrite nf_multiplicity_big. 
 rewrite nf_multiplicity_head.
 discriminate 1.
 auto.
 auto.
 constructor;auto.
 subst l'1.
 unfold equiv in H2. 
 generalize (H2 a). 
 rewrite nf_multiplicity_head.
 rewrite nf_multiplicity_head.
 injection 1;intro; subst n0.
  rewrite (IHnf2 (cons t n1 t0)).
 auto.
 apply equiv_tail with  a n.
 unfold equiv;auto.
 inversion H3;auto.
 auto.
 constructor;auto.
 intros.
 generalize (H2 a).
 rewrite nf_multiplicity_head.
 rewrite nf_multiplicity_big.
 discriminate 1.
 auto.
 auto.
 constructor;auto.
Qed.



 
