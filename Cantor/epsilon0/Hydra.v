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
Require Import List.
Require Import EPSILON0.
Require Import MSE0.



(* An hydra is a finitely branched tree *)

Inductive Hydra : Set :=
|  head : Hydra
|  node : Hydrae -> Hydra
with Hydrae : Set :=
| single : Hydra -> Hydrae
| hcons : Hydra -> Hydrae -> Hydrae.

(* a small example *)
Definition Lerne: Hydra :=
 node (hcons head
        (single (node (hcons
                        (node (hcons (node (single head))
                               (single (node (hcons head (single head))))))
                        (single head))))).
 
Scheme Hydra_rect2 := Induction for Hydra Sort Type
with   Hydrae_rect2 := Induction for Hydrae Sort Type.


(* occurrences = lists of nats *)
Definition occurrence := list nat.


(* reaction of the Hydra : the occurrence parameter points to
   the head just removed *)


(* reduction at distance 1 from the root *)

(* one head is removed, and no new head is built *)
Open Scope list_scope.
(* mettre u comme metavariable pour les occurrences *)

Inductive S1 : occurrence -> Hydrae -> Hydrae -> Set :=
| S1_first : forall s, S1 (0::nil) (hcons head s) s
| S1_last : forall h, S1 (1::nil) (hcons h (single head)) (single h)
| S1_rest : forall i h s s', S1 (i::nil)%list s s' ->
                               S1 (S i::nil) (hcons h s)
                                   (hcons h s').


Inductive R1 : occurrence -> Hydra -> Hydra -> Set :=
| R1_single : R1 (0::nil) (node (single head)) head
| R1_node   : forall u l l', S1 u l l' ->
                         R1 u (node l) (node l').


(* reduction at distance 2 from the root *)

(* some head at level 2 is cut, the new level 1 sub_hydra is replicated
   n times *)

Fixpoint replicate (h:Hydra)(n:nat)(s:Hydrae){struct n}:Hydrae :=
  match n with 
  | 0 => s
  | S p => hcons h (replicate h p s)
  end.


Inductive S2 (n:nat) : occurrence -> Hydrae -> Hydrae ->  Set :=
| S2_single : forall oc h h', R1 oc h h' ->
                             S2 n (0::oc) (single h)
                                   (replicate h' n (single h'))
| S2_first : forall oc h h' s, R1 oc h h' ->
                              S2 n (0::oc) (hcons h s)
                                    (replicate h' (S n) s)

| S2_rest  : forall oc ocs  h s s', S2 n (oc::ocs) s s' ->
                                S2 n (S oc::ocs) (hcons h s)
                                          (hcons h s').

(* reduction at any level >= 2 *)

Inductive Rn (n:nat) : occurrence -> Hydra -> Hydra -> Set :=

| Rn_here : forall u l l', S2 n u l l' ->
                             Rn n u (node l) (node l')
| Rn_plus : forall u l l', Sn n u l l' ->
                             Rn n u (node l) (node l')
with Sn (n:nat) : occurrence -> Hydrae -> Hydrae -> Set :=
|  Sn_single : forall u h h', Rn n u h h' ->
                                   Sn n (0::u) 
                                       (single h) (single h')

|  Sn_first : forall h h' u r, Rn n u h h'->
                                   Sn n (0::u) 
                                              (hcons h r) (hcons h' r)

|  Rnl_rest : forall h  occ u r r', Sn n (occ::u)r r' ->
                                  Sn n (S occ::u) 
                                              (hcons h r) (hcons h r').



Scheme Rn_rect2 := Induction for Rn Sort Type
with   Sn_rect2 := Induction for Sn Sort Type.


(* general decapitation-grow relationship : 
   n is the replication factor (chosen by the hydra ) *)

Inductive Rh (n:nat) : occurrence -> Hydra -> Hydra -> Set :=
 depth1 : forall occ h h', R1 occ h h' -> Rh n occ h h'
|depth2 : forall occ h h', Rn n occ h h' -> Rh n occ h h'.

(* an hydra of size > 1 is always tranformed by any factor *)


Inductive Sh (n:nat) : occurrence -> Hydrae -> Hydrae -> Set :=
| Sh_1 : forall occ l l', S1 occ l l' -> Sh n occ l l'
| Sh_2 : forall occ l l', S2 n occ l l' -> Sh n occ l l'
| Sh_3 : forall occ l l', Sn n occ l l' -> Sh n occ l l'.


Fixpoint head_at (h:Hydra)(o:occurrence) {struct h}: bool :=
 match h, o with head, nil => true
               | node hs, o => head_at_l hs o
               | _, _ => false
 end
with head_at_l (hs:Hydrae)(o:occurrence){struct hs} : bool :=
 match hs, o with single h, 0::o' => head_at h o'
                | hcons h hs', 0::o' => head_at h o'
                | hcons h hs', S p::o' => head_at_l hs' (p::o')
                | _, _ => false
end.


Lemma head_at_nil : forall h, head_at h nil = true ->
                               h = head.
Proof.
 destruct h; simpl; auto.
 case h; simpl; discriminate 1 .
Qed.


Lemma head_at_zero_nil : forall h, head_at h (0::nil) = true ->
   {h' : Hydrae | h = node (hcons head h')} + {h = node (single head)}.
Proof.
 destruct h.
 simpl.
 discriminate 1.
 case h;simpl.
 destruct h0.
 right;auto.
 simpl.
 case h0.
 simpl.
 discriminate 1.
 simpl.
 discriminate 1.
 destruct h0.
 simpl.
 left;exists h0;auto.
 simpl.
 case h0.
 simpl.
 discriminate 1.
 simpl.
 discriminate 1.
Qed.

Lemma head_at_S_nil : forall h p, head_at h (S p::nil) = true ->
   {h' : Hydrae & {h0 : Hydra | h = node (hcons h0 h') /\ 
                                head_at_l h' (p::nil) = true}}.
Proof.
 destruct h.
 simpl.
 discriminate 1.
 case h;simpl.
 discriminate 1.
 intros h0 h1 p;exists h1;exists h0;auto.
Qed.


Lemma head_at_O_cons : forall h l p, head_at h (0::p::l) = true ->
    {h0:Hydra & {h' : Hydrae | h = node (hcons h0 h') /\
                     head_at h0 (p::l) = true}} + 
    {h0:Hydra | h = node (single h0) /\ head_at h0 (p::l) = true}.
Proof.
 destruct h.
 simpl.
 discriminate 1.
 case h.
 simpl.
 right.
 exists h0.
 auto.
 simpl.
 left.
 exists h0;exists h1;auto.
Qed.


Lemma head_at_S_cons : forall h l q p, head_at h (S q::p::l) = true ->
    {h0:Hydra & {h' : Hydrae | h = node (hcons h0 h') /\
                               head_at_l h' (q::p::l) = true}}.
Proof.
 destruct h.
 simpl.
 discriminate 1.
 case h.
 simpl.
 discriminate 1.
 simpl.
 intros h0 h1 l q p. 
 exists h0;exists h1.
 auto.
Qed.


Lemma head_at_l_nil : forall h, head_at_l h nil = true ->
                               False.
Proof.
 destruct h; simpl;  discriminate 1 .
Qed.


Lemma head_at_l_zero_nil : forall h, head_at_l h (0::nil) = true ->
   {h' : Hydrae | h = (hcons head h')} + {h = (single head)}.
Proof.
 destruct h.
 simpl.
 case h.
 right;auto.
 simpl.
 destruct h0.
 simpl.
 discriminate 1.
 simpl.
  discriminate 1.
 simpl.
 case h.
 simpl.
 left; exists h0;auto.
 simpl.
 intros.
 case (head_at_l_nil _  H).
Qed.


Lemma head_at_l_S_nil : forall h p, head_at_l h (S p::nil) = true ->
   {h' : Hydrae & {h0 : Hydra | h =  (hcons h0 h') /\ 
                                head_at_l h' (p::nil) = true}}.
Proof.
 destruct h.
 simpl.
 discriminate 1.
 simpl.
 exists h0; exists h; auto.
Qed.



Lemma head_at_l_O_cons : forall h l p, head_at_l h (0::p::l) = true ->
    {h0:Hydra & {h' : Hydrae | h =  (hcons h0 h') /\
                               head_at h0 (p::l) = true}} + 
    {h0:Hydra | h =  (single h0) /\ head_at h0 (p::l) = true}.
Proof.
 destruct h.
 simpl.
 case h.
 simpl.
 discriminate 1.
 right.
 exists (node h0);auto.
 left.
 exists h.
 exists h0.
 split;auto.
Qed.

Lemma head_at_l_S_cons : forall h l q p, head_at_l h (S q::p::l) = true ->
    {h0:Hydra & {h' : Hydrae | h =  (hcons h0 h') /\
                               head_at_l h' (q::p::l) = true}}.
Proof.
 destruct h.
 simpl.
 discriminate 1.
 intros.
 exists h;exists h0; split;auto.
Qed.


Lemma S1_head : forall o h h', S1 o h h' -> 
                                    head_at_l h o = true.
Proof.
 induction 1;  simpl; auto.
Qed.


Lemma R1_head : forall o h h', R1 o h h' -> head_at h o = true.
Proof.
 induction 1; simpl; auto.
 eapply S1_head; eauto.
Qed.


Lemma S2_head : forall n o h h', S2 n o h h' -> head_at_l h o =
                                                          true.
Proof.
 induction 1; simpl; auto;
 eapply R1_head; eauto.
Qed.

Lemma Rn_head : forall n o h h', Rn n o h h' -> head_at h o = true.
Proof.
 intros n o h h0 H.
 pattern o, h, h0, H.
 elim H using Rn_rect2  with 
     (P0 := fun o h h0 (H: Sn n o h h0) => 
                       head_at_l h o = true); simpl;auto.
 intros.
 generalize (S2_head n u l l' s).
 simpl.
 auto.
Qed.


Lemma Rh_head : forall n o h h', Rh n o h h' -> head_at h o = true.
Proof.
 destruct 1.
 eapply R1_head; eauto.
 eapply Rn_head.
 eauto.
Qed.

Lemma Sh_head : forall n o h h', Sh n o h h' -> 
                       head_at_l h o = true.
Proof.
 destruct 1.
 eapply S1_head; eauto.
 eapply S2_head.
 eauto.
 elim s.
 simpl.
 intros;eapply Rn_head;eauto.
 simpl.
 intros;eapply Rn_head;eauto.
 simpl; auto.				
Qed.


Lemma Hydra_answers_nil :
 forall h, h <> head -> head_at h nil = false.
Proof.
 intro h;case h;simpl.
 intro; absurd (head = head);auto.
 destruct h0;simpl;auto.
Qed.

(* quite long, huh ? *)

Lemma Hydra_answers :
 forall h u n, h <> head -> head_at h u = true ->
                 {h':Hydra & Rh n u h h'}.  
Proof.
 intro h; 
 elim h using Hydra_rect2 with
        (P0 := fun hs => hs <>  (single head) -> 
                         forall u n, head_at_l hs u = true ->
                                    {h':Hydrae & Sh n u hs h'}).
 intros; absurd (head=head);auto.
 destruct u.
 simpl.
 intros. 
 case (head_at_l_nil _ H1).
 case u.
 case n.
 intros.
 case (head_at_zero_nil _ H1).
 destruct 1.
 injection e.
 intros; subst h0.
 exists (node x).
 left.
 constructor.
 constructor.
 injection 1.
 intro; subst h0.
 exists head.
 left.
 constructor .
 intros.
 case (head_at_S_nil _ _ H1).
 destruct 1.
 case a.
 intros.
 injection H2. 
 intro; subst h0.
 assert( hcons x0 x <> single head).
 discriminate.
 case (H H4 (S n0::nil) n1  H1).
 

 intros;exists (node x1).
 case s.
 left.
 constructor;auto.
 right.
 left;auto.
 right;auto.
 right;auto.
 case n.
 intros.
 simpl in H1.
 case (head_at_l_O_cons _ _ _ H1).
 destruct 1.
 case s.
 destruct 1.
 assert (h0 <> single head).
 rewrite H2;discriminate.
 case (H H4 (0::n0::l) n1 H1).
 intro x1;exists (node x1).
 case s0.
 left; constructor.
 auto.
 right;left.
 auto.
 right.
 right.
 auto.
 destruct 1. 
 case a;intros.
 clear a.
 subst h0.
 assert (single x <> single head).
 red; intro. 
 injection H2;intro; subst x.
 simpl in H1.
 discriminate H1.
 case (H H2 (0::n0::l) n1).
 auto.
 intros;exists (node x0).
 case s.
 left;constructor.
 auto.
 right;left.
 auto.
 right;right.
 auto.
 simpl.
 intros.
 assert( h0 <> single head).
 red;intro; subst h0.
 discriminate H1.
 case (H H2 _ n2 H1).
 intros; exists (node x).
 case s.
 left;auto.
 constructor;auto.
 right;left;auto.
 right;right.
 auto.
 destruct u.
  simpl.
 discriminate 1.
 destruct n.
 simpl.
 assert (h0 <> head).
 red;intro;apply H0;subst h0;auto.
 intros.
 case (H u n H1 H2).
 destruct 1.
 exists (replicate h' n (single h')).
 constructor 2. 
 constructor.
 auto.
 exists (single h').
 constructor 3.
 constructor;auto.
 simpl.
 discriminate 1.
 destruct u.
 intros.
 case (head_at_l_nil _ H2).
 case n.
 simpl.
 case u.
 intros.
 assert (h0=head).
 apply head_at_nil.
 auto.
 subst h0.
 exists h1.
 constructor 1;constructor.
 destruct n0.
 intros.
 assert (h0 <> head).
 red;intro;subst h0.
 discriminate H2.
 case (H (0::l) n0 H3 H2).
 destruct 1.
 exists (replicate h' (S n0) h1).
 constructor 2.
 constructor.
 auto.
 exists (hcons h' h1).
 constructor 3.
 constructor.
 auto.
 simpl.
 intros.
 assert (h0 <> head).
 red;intro;subst h0;discriminate H2.
 case (H (S n0::l) n1 H3 H2).
 destruct 1.
 exists (replicate h' (S n1) h1).
 constructor 2.
 constructor 2.
 auto.
 exists (hcons h' h1).
 constructor 3.
 constructor 2.
 auto.
 intros.
 simpl in H2.
 generalize H2; case n0;case u.
 simpl.
 intros.
 case (head_at_l_zero_nil _ H3).
 destruct 1.
 assert (h1 <> single head).
 rewrite e; discriminate.
 case (H0 H4 (0::nil) n1).
 auto.
 inversion 1.
 exists (hcons h0 x0).
 constructor 1.
 constructor 3.
 auto.
 exists (hcons h0 x0).
 constructor 2.
 constructor 3.
 auto.
 exists (hcons h0 x0).
 constructor 3.
 constructor 3.
 auto.
 intro H4;subst h1.
 exists (single h0).
 constructor 1.
 constructor.
 intros.
 assert (h1 <> single head).
 intro ; subst h1; discriminate H3.
 case (H0 H4 (0::n2::l) n1 H3).
 inversion 1.
 exists (hcons h0 x).
 constructor 1.
 inversion H5.
 exists (hcons h0 x). 
 constructor 2.
 constructor 3.
 auto.
 exists (hcons h0 x). 
 constructor 3.
 constructor 3.
 auto.
 intros; assert (h1 <> single head).
 intro; subst h1;discriminate H3.
 case (H0 H4 (S n2::nil) n1 H3).
 inversion 1.
 exists (hcons h0 x).
 constructor 1.
 constructor 3.
 auto.
 exists (hcons h0 x).
 constructor 2.
 constructor 3;auto.
 exists (hcons h0 x).
 constructor 3.
 constructor 3.
 auto.
 intros.
 assert (h1 <> single head).
 red;intro;subst h1;discriminate H3.
 case (H0 H4 _ n1 H3).
 inversion 1.
 inversion H5.
 exists (hcons h0 x).
 constructor 2.
 constructor 3.
 auto.
 exists (hcons h0 x).
 constructor 3.
 constructor 3.
 auto.
Defined.


(* converting an hydra into an ordinal notation *)

(* it would be better (i.e. more abstract) to omega-raise 
   the h2o of the sub_hydrae before sorting.
   (nearer to the concept of natural sum)
 
*)



Fixpoint h2o (h:Hydra) : T1 :=
  match h with head => zero
             | node hs => (sort (h2ol hs))
end 
with h2ol (hs:Hydrae) : T1 :=
  match hs with single h => (cons (h2o h) 0 zero)
              | hcons h hs' => (cons (h2o h) 0 (h2ol hs'))
 end.


Theorem h2o_nf : forall h, nf (h2o h).
Proof.
 intro h; elim h using Hydra_rect2 
            with (P0 := fun hs => nfs (h2ol hs)).
 simpl.
 constructor.
 simpl.
 intros.
 apply sort_nf.
 auto.
  intros;apply nf_to_nfs.
  simpl.
 constructor.
 auto.
 simpl;auto.
 constructor;auto.
Qed.



Theorem h2ol_nfs : forall hs, nfs (h2ol hs).
Proof.
 induction hs.
  simpl.
  constructor.
  apply h2o_nf.
  constructor.
 simpl;constructor.
 apply h2o_nf.
 auto.
Qed.


(*
Let l l' be lists of hydras, if l' is obtained from l by removing
some element of l (which must be a head), then multiset of ordinal terms 
associed with l is lesser than the multiset associed with l' 
*)

Lemma S1_decrease:
  forall u l l', S1 u l l' -> exists a, ltM a (h2ol l') (h2ol l).
Proof.
 induction 1.
 simpl.
 exists zero.
 apply ltM_tail;auto.
 simpl.
 exists zero.
 unfold ltM.
 split.
 Opaque T1_eq_dec.
 simpl; case (T1_eq_dec (h2o h) zero).
 intro e; rewrite e; simpl.
 case (T1_eq_dec zero zero).
 auto with arith.
 intros; absurd (zero=zero);auto.
 case (T1_eq_dec zero (h2o h)).
 intros; absurd (zero = h2o h);auto.
 case (T1_eq_dec zero zero).
 auto.
 intro; absurd (zero=zero).
 auto.
 auto.
 simpl.
 intros;case (T1_eq_dec b (h2o h)).
 intros;case (T1_eq_dec b zero).
 intro; clear e; subst b; inversion H.
 auto.
 intros;case (T1_eq_dec b zero).
 intro;  subst b; inversion H.
 auto.
 simpl.
 case IHS1; intros a Ha;exists a; apply ltM_cons;auto.
Qed.

(* 
  If h' is obtained from h by removing a head at distance 1 from its root,
  then the ordinal term associed with h' is lesser than the ordinal term
  associed with h
*)

Lemma R1_decrease : forall u h h', R1 u h h' -> h2o h' <  h2o h.
Proof.
 induction 1.
 simpl.
 auto with T1.
 simpl.
 generalize (S1_decrease u l l' s).
 destruct 1.
 generalize (sort_equiv (h2ol l)).
 intro He.
 generalize (sort_equiv (h2ol l')).
 intro He'.
 generalize (sort_nf (h2ol l)).
 intro Hs.
 generalize (sort_nf (h2ol l')).
 intro Hs'.
 apply ltM_lt with x ; auto.
 apply sort_nf.
 apply h2ol_nfs.
  apply sort_nf.
 apply h2ol_nfs.
 eapply ltM_equiv_ltM.
 2:eauto.
 eapply ltM_equiv_ltMR.
 eauto.
 auto.
Qed.


(* 
  Let l l' be lists of hydras.
  
  Let us assume than l' is obtained fromp l by
  a) choosing an hydra li element of l
  b) chopping off a head from li (at distance 1 from its root)
  c) replicating n times the decapited hydra 

  then the multiset of ordinal terms associed to l' is lesser than
   the multiset associed with l
*)


Lemma S2_decrease : forall n u l l', S2 n u l l' ->
                                        exists a:T1, 
                                          ltM a (h2ol l') (h2ol l).
Proof.
 induction 1.
 simpl.
 generalize (R1_decrease _ _ _ r).
 exists (h2o h).
 induction n.
 simpl.
 apply ltM_head.
 auto with arith.
 auto.
 simpl.
 apply lt_ltM.
 auto.
 auto.
 exists (h2o h).
 induction n.
 simpl.
 apply ltM_head.
 auto with arith.
 eapply R1_decrease.
 eauto.
 simpl.
 simpl in IHn.
 apply lt_ltM.
 eapply R1_decrease.
 eauto.
 auto.
 case IHS2; intros.
 exists x.
 simpl.
 apply ltM_cons.
 auto.
Qed.


(*

If h' is obtained from h by
 a) chopping off a head at a level >= 2 
 b) letting the hydra react
 
 then the mesaure associed with h' is lesser than the measure associed with h

*)

Theorem Rn_decrease : forall n u h h', Rn n u h h' -> 
                                        h2o h' <  h2o h.
Proof.
 intros n o h h' H.
 elim H using Rn_rect2 with
   (P0 := fun o (h h0: Hydrae)(H:Sn n o h h0) => 
                    exists a, ltM a (h2ol h0) (h2ol h)).
 simpl;intros. 
 case (S2_decrease _ _ _ _ s).
 intros.
 eapply ltM_lt with x.
 apply sort_nf. 
 apply h2ol_nfs. 
 apply sort_nf.
 apply h2ol_nfs. 
 
eapply ltM_equiv_ltM.
 2:eapply sort_equiv.
 
 eapply ltM_equiv_ltMR.
 2:eapply sort_equiv.
 auto.
 intros.
 case H0;intros a Ha.
 apply ltM_lt with a;auto.
 apply h2o_nf.
 apply h2o_nf.
  simpl.
  eapply ltM_equiv_ltM.
 2:eapply sort_equiv.
 eapply ltM_equiv_ltMR.
 2:eapply sort_equiv.
 auto.

 intros.
 exists (h2o h0).
 simpl. apply ltM_head.
 auto .
 intros.
 exists (h2o h0).
 simpl;apply ltM_head.
 auto with arith.
 intros.
 case H0.
 intros.
 exists x.
 simpl;apply ltM_cons;auto.
Qed.



Theorem Rh_decrease : forall n u h h', Rh n u h h' -> h2o h' <  h2o h.
Proof.
 induction 1.
 eapply R1_decrease.
 eauto.
 eapply Rn_decrease.
 eauto.
Qed.

Definition Hercules_strat := nat ->  Hydra -> occurrence.

Definition Hydra_strat := nat -> Hydra -> occurrence -> nat.

Section game.
 Variable str : Hercules_strat.
 Hypothesis str_ok : forall t h, head_at h (str t h) = true.
 Variable str_hy : Hydra_strat.


 Inductive Hercules_wins  :  nat -> Hydra  -> Prop :=
    Now  : forall t, Hercules_wins t head
 |  Later  : forall t h , ( forall h', Rh (str_hy (S t) h (str (S t) h)) 
                                           (str (S t) h) h h' ->
                                        Hercules_wins t h' ) ->
            Hercules_wins t h.



Definition Hercules_ok (alpha:T1) := forall t h, h2o h = alpha -> 
   Hercules_wins t h.
 

Lemma Winner : forall alpha, nf alpha -> Hercules_ok alpha.
Proof.
 intros o Ho;  apply  EPSILON0.transfinite_induction.
 2:auto.
 intros.
 unfold Hercules_ok.
 destruct h.
 constructor.
 unfold Hercules_ok in H0.
 intro.
 right.
 intros.
 generalize  (H0 (h2o h') ).
 intros; eapply H0.
 3:reflexivity.
 apply h2o_nf.
 case H1.
 eapply Rh_decrease.
 eauto.
Qed.


Theorem Legend : forall t h, Hercules_wins t h.
Proof.
 generalize Winner.
 unfold Hercules_ok.
 intros.
 eapply H.
 eapply h2o_nf.
 reflexivity.
Qed.

End game.

Transparent T1_eq_dec.






 



