Require Import Rewriting.
Require Import Equality.

Set Implicit Arguments.

(*
  We construct the weakly orthogonal TRS with rules

    PS : P(S(x)) -> x
    SP : S(P(x)) -> x

  and show it is a counterexample to UN-inf.

  J. Endrullis, C. Grabmayer, D. Hendriks, J.W. Klop and V. van Oostrom
  Unique Normal Forms in Infinitary Weakly Orthogonal Rewriting
  Rewriting Techniques and Applications, 2010

  Because we have S as nat constructor, we rename the function symbol
  to D and U (up, down).

  Let psi = U^1 D^2 U^3 D^4, we show:

  * This TRS is weakly orthogonal
  * psi rewrites to DDD...
  * psi rewrites to UUU...
  * DDD... is a normal form
  * UUU... is a normal form
  * DDD... and UUU... are not bisimilar
*)

(* Signature *)

Inductive symbol : Set := D | U.

Definition beq_symb (f g : symbol) : bool :=
  match f, g with
  | D, D => true
  | U, U => true
  | _, _ => false
end.

Lemma beq_symb_ok : forall f g, beq_symb f g = true <-> f = g.
Proof.
(* This should work for any finite inductive symbol type *)
intros f g.
split; intro H.
(* beq_symb f g = true -> f = g *)
  destruct f; destruct g; simpl; (reflexivity || discriminate).
(* f = g ->  beq_symb f g = true *)
  subst g; destruct f; simpl; reflexivity.
Qed.

Definition arity (f : symbol) : nat :=
  match f with
  | D => 1
  | U => 1
  end.

(* Variables *)

(* We only need one variable *)
Definition variable : Set := unit.

Fixpoint beq_var (x y : variable) : bool := true.

Lemma beq_var_ok : forall x y, beq_var x y = true <-> x = y.
Proof.
intros [] []; split; reflexivity.
Qed.

(* Terms *)

Definition F : signature := Signature arity beq_symb_ok.
Definition X : variables := Variables beq_var_ok.

Notation term := (term F X).
Notation fterm := (finite_term F X).

(* Variables *)
Notation "x !" := (@FVar F X x) (at level 75).

(* Function application with one argument *)
Notation "f @ a" := (@Fun F X f (vcons a (vnil term))) (right associativity, at level 75).
Notation "f @@ a" := (@FFun F X f (vcons a (vnil fterm))) (right associativity, at level 75).

(* UUU... *)
CoFixpoint repeat_U : term :=
  U @ repeat_U.

(* DDD... *)
CoFixpoint repeat_D : term :=
  D @ repeat_D.

(* DUDU... *)
(* TODO: better to define repeat_DU and repeat_UD together? *)
CoFixpoint repeat_DU : term :=
  D @ U @ repeat_DU.

(* U^n t *)
Fixpoint Unt (n : nat) t :=
  match n with
  | O   => t
  | S n => U @ (Unt n t)
  end.

(* D^n t *)
Fixpoint Dnt (n : nat) t :=
  match n with
  | O   => t
  | S n => D @ (Dnt n t)
  end.

(* U^2n t *)
Fixpoint U2nt (n : nat) t :=
  match n with
  | O   => t
  | S n => U @ U @ (U2nt n t)
  end.

(* D^2n t *)
Fixpoint D2nt (n : nat) t :=
  match n with
  | O   => t
  | S n => D @ D @ (D2nt n t)
  end.

(* D^n U^n t *)
Definition DnUnt n t : term :=
  Dnt n (Unt n t).

(* U^n D^n t *)
Definition UnDnt n t : term :=
  Unt n (Dnt n t).

(* D^2n U^2n t *)
Definition D2nU2nt n t : term :=
  D2nt n (U2nt n t).

(* U^2n D^2n t *)
Definition U2nD2nt n t : term :=
  U2nt n (D2nt n t).

Lemma term_bis_U :
  forall t s,
    t [~] s -> (U @ t) [~] (U @ s).
Proof.
intros t s H.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
assumption.
Qed.

Lemma term_bis_D :
  forall t s,
    t [~] s -> (D @ t) [~] (D @ s).
Proof.
intros t s H.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
assumption.
Qed.

Lemma term_eq_up_to_n_Unt_repeat_U :
  forall n t,
    term_eq_up_to n (Unt n t) repeat_U.
Proof.
induction n as [| n IH]; simpl; intro t.
constructor.
rewrite (peek_eq repeat_U); simpl.
constructor.
intro i.
dependent destruction i.
apply IH.
dependent destruction i.
Qed.

Lemma term_eq_up_to_n_Dnt_repeat_D :
  forall n t,
    term_eq_up_to n (Dnt n t) repeat_D.
Proof.
induction n as [| n IH]; simpl; intro t.
constructor.
rewrite (peek_eq repeat_D); simpl.
constructor.
intro i.
dependent destruction i.
apply IH.
dependent destruction i.
Qed.

Lemma term_bis_Unt :
  forall n t s,
    t [~] s -> Unt n t [~] Unt n s.
Proof.
induction n; intros t s H; simpl.
assumption.
apply term_bis_U.
apply IHn.
assumption.
Qed.

Lemma term_bis_Dnt :
  forall n t s,
    t [~] s -> Dnt n t [~] Dnt n s.
Proof.
induction n; intros t s H; simpl.
assumption.
apply term_bis_D.
apply IHn.
assumption.
Qed.

Lemma term_bis_U2nt :
  forall n t s,
    t [~] s -> U2nt n t [~] U2nt n s.
Proof.
induction n; intros t s H; simpl.
assumption.
apply term_bis_U.
apply term_bis_U.
apply IHn.
assumption.
Qed.

Lemma term_bis_D2nt :
  forall n t s,
    t [~] s -> D2nt n t [~] D2nt n s.
Proof.
induction n; intros t s H; simpl.
assumption.
apply term_bis_D.
apply term_bis_D.
apply IHn.
assumption.
Qed.

Lemma UUnt_eq_UnUt :
  forall n t,
    (U @ Unt n t) = Unt n (U @ t).
induction n; intro t.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Lemma DDnt_eq_DnDt :
  forall n t,
    (D @ Dnt n t) = Dnt n (D @ t).
induction n; intro t.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Lemma UU2nt_eq_U2nUt :
  forall n t,
    (U @ U2nt n t) = U2nt n (U @ t).
induction n; intro t.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Lemma DD2nt_eq_D2nDt :
  forall n t,
    (D @ D2nt n t) = D2nt n (D @ t).
induction n; intro t.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Lemma DSnUSnt_eq_DDnUnUt :
  forall n t,
    DnUnt (S n) t = (D @ (DnUnt n (U @ t))).
Proof.
intros n t.
unfold DnUnt.
simpl.
rewrite UUnt_eq_UnUt.
reflexivity.
Qed.

Lemma USnDSnt_eq_UUnDnDt :
  forall n t,
    UnDnt (S n) t = (U @ (UnDnt n (D @ t))).
Proof.
intros n t.
unfold UnDnt.
simpl.
rewrite DDnt_eq_DnDt.
reflexivity.
Qed.

Lemma D2SnU2Snt_eq_DDD2nU2nUUt :
  forall n t,
    D2nU2nt (S n) t = (D @ D @ (D2nU2nt n (U @ U @ t))).
Proof.
intros n t.
unfold D2nU2nt.
simpl.
rewrite UU2nt_eq_U2nUt.
rewrite UU2nt_eq_U2nUt.
reflexivity.
Qed.

Lemma U2SnD2Snt_eq_UUU2nD2nDDt :
  forall n t,
    U2nD2nt (S n) t = (U @ U @ (U2nD2nt n (D @ D @ t))).
Proof.
intros n t.
unfold U2nD2nt.
simpl.
rewrite DD2nt_eq_D2nDt.
rewrite DD2nt_eq_D2nDt.
reflexivity.
Qed.

Lemma D2nU2nt_eq_D2nU2nt :
  forall n t,
    D2nU2nt n t = DnUnt (2 * n) t.
Proof.
induction n; intro t; simpl.
unfold D2nU2nt, D2nt, U2nt, DnUnt, Dnt, Unt.
reflexivity.
rewrite D2SnU2Snt_eq_DDD2nU2nUUt.
rewrite DSnUSnt_eq_DDnUnUt.
rewrite IHn with (U @ U @ t).
simpl.
rewrite (eq_sym (plus_n_Sm n (n + 0))).
rewrite DSnUSnt_eq_DDnUnUt.
reflexivity.
Qed.

(*
   We would like to define psi' like this

     CoFixpoint psi' n : term :=
       Unt n (Dnt (S n) (psi' (S (S n)))).

   but unfortunately this is not guarded.
*)

(* D^n U^Sn D^SSn U^SSSn ... *)
CoFixpoint psi' n : term :=
  (cofix D2nDt (d : nat) :=
    match d with
    | O   => D @ (cofix U2nt (u : nat) :=
               match u with
               | O   => psi' (S n)
               | S u => U @ U @ (U2nt u)
               end) (S n)
    | S d => D @ D @ (D2nDt d)
    end) n.

(* DUUDDDUUUU... *)
Definition psi := psi' 0.

Lemma UU2nt_eq_U2nUt_unfolded :
  forall n t,
    (U @ (cofix U2nt (u : nat) : term :=
            match u with
            | 0 => t
            | S u0 => U @ U @ U2nt u0
            end) n)
    =
    (cofix U2nt (u : nat) : term :=
       match u with
       | 0 => U @ t
       | S u0 => U @ U @ U2nt u0
       end) n.
Proof.
induction n; intro t.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
        match u with
        | 0 => t
        | S u0 => U @ U @ U2nt u0
        end) 0)).
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ U @ U2nt u0
      end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) (S n))).
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ U @ U2nt u0
      end) (S n))).
simpl.
rewrite IHn with t.
reflexivity.
Qed.

Lemma psin_eq_DD2nU2nUUpsiSn :
  forall n,
    psi' n = (D @ (D2nU2nt n (U @ U @ (psi' (S n))))).
Proof.
intro n.
rewrite (peek_eq (psi' n)).
simpl.
generalize (psi' (S n)).
induction n; intro t.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) 1)).
unfold D2nU2nt.
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
                 match u with
                 | 0 => t
                 | S u0 => U @ U @ U2nt u0
                 end) (S (S n)))).
rewrite D2SnU2Snt_eq_DDD2nU2nUUt.
simpl.
rewrite UU2nt_eq_U2nUt_unfolded with (S n) t.
rewrite UU2nt_eq_U2nUt_unfolded with (S n) (U @ t).
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
       match d with
       | 0 =>
           D @
           (cofix U2nt (u : nat) : term :=
              match u with
              | 0 => U @ U @ t
              | S u0 => U @ U @ U2nt u0
              end) (S n)
       | S d0 => D @ D @ D2nDt d0
       end) n)).
simpl.
rewrite IHn with (U @ U @ t).
reflexivity.
Qed.

Lemma psin_eq_DS2nUS2nUpsiSn :
  forall n,
    psi' n = DnUnt (S (2 * n)) (U @ (psi' (S n))).
Proof.
intro n.
rewrite psin_eq_DD2nU2nUUpsiSn.
rewrite D2nU2nt_eq_D2nU2nt.
rewrite DSnUSnt_eq_DDnUnUt.
reflexivity.
Qed.

(* Contexts *)

Notation context := (context F X).

(* Function application with one argument *)
Notation "f @@@ a" := (@CFun F X f 0 0 (@refl_equal nat (arity f)) (vnil term) a (vnil term)) (right associativity, at level 75).

Fixpoint Dnc n c : context :=
  match n with
  | O   => c
  | S n => D @@@ (Dnc n c)
  end.

Fixpoint Unc n c : context :=
  match n with
  | O   => c
  | S n => U @@@ (Unc n c)
  end.

Lemma fill_Dnc_t :
  forall n c t,
    fill (Dnc n c) t = Dnt n (fill c t).
Proof.
induction n.
reflexivity.
intros c t.
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma fill_Unc_t :
  forall n c t,
    fill (Unc n c) t = Unt n (fill c t).
Proof.
induction n.
reflexivity.
intros c t.
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma fill_DnHole_t :
  forall n t,
    fill (Dnc n Hole) t = Dnt n t.
Proof.
intros n t.
apply fill_Dnc_t.
Qed.

Lemma fill_UnHole_t :
  forall n t,
    fill (Unc n Hole) t = Unt n t.
Proof.
intros n t.
apply fill_Unc_t.
Qed.

Lemma fill_DmUnc_t :
  forall m n c t,
    fill (Dnc m (Unc n c)) t = Dnt m (Unt n (fill c t)).
Proof.
intros m n c t.
rewrite fill_Dnc_t.
rewrite fill_Unc_t.
reflexivity.
Qed.

Lemma fill_UmDnc_t :
  forall m n c t,
    fill (Unc m (Dnc n c)) t = Unt m (Dnt n (fill c t)).
Proof.
intros m n c t.
rewrite fill_Unc_t.
rewrite fill_Dnc_t.
reflexivity.
Qed.

Lemma fill_DmUnHole_t :
  forall m n t,
    fill (Dnc m (Unc n Hole)) t = Dnt m (Unt n t).
Proof.
intros m n t.
apply fill_DmUnc_t.
Qed.

Lemma fill_UmDnHole_t :
  forall m n t,
    fill (Unc m (Dnc n Hole)) t = Unt m (Dnt n t).
Proof.
intros m n t.
apply fill_UmDnc_t.
Qed.

(* Rewriting *)

Notation trs := (trs F X).

(* We use this variable in the rewrite rules *)
Definition varx : X := tt.

(* DUx -> x *)
Definition DU_l : fterm := D @@ U @@ varx!.
Definition DU_r : fterm := varx!.

Lemma DU_wf :
  is_var DU_l = false /\
  incl (vars DU_r) (vars DU_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition DU : rule := Rule DU_l DU_r DU_wf.

(* UDx -> x *)
Definition UD_l : fterm := U @@ D @@ varx!.
Definition UD_r : fterm := varx!.

Lemma UD_wf :
  is_var UD_l = false /\
  incl (vars UD_r) (vars UD_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition UD : rule := Rule UD_l UD_r UD_wf.

Definition UD_trs : trs := DU :: UD :: nil.

Lemma UD_left_linear :
  trs_left_linear UD_trs.
Proof.
constructor; [| constructor];
  unfold left_linear; unfold linear; simpl;
    constructor.
intro; assumption.
constructor.
intro; assumption.
constructor.
Qed.

Lemma UD_critical_pairs_trivial :
  forall t1 t2,
    critical_pair UD_trs t1 t2 ->
    t1 [~] t2.
Proof.
intros t1 t2 H.
unfold critical_pair in H.
destruct H as [r1 [r2 [[| [| a] [| [| b] [| c p]]] [sigma [tau [[Hr1 | [Hr1 | []]] [[Hr2 | [Hr2 | []]] [T H]]]]]]]];
rewrite <- Hr1 in * |-;
rewrite <- Hr2 in * |-;
clear r1 r2 Hr1 Hr2;
try (contradict T; auto; fail);
clear T;
try (contradict H; fail); simpl in H;
destruct H as [V [H [H1 H2]]];
try (contradict V; fail);
apply (term_bis_trans H1); apply term_bis_symm; apply (term_bis_trans H2);
clear H1 H2;
dependent destruction H; specialize H with (First (n := 0)); unfold vmap in H; simpl in H;
dependent destruction H; specialize H with (First (n := 0)); unfold vmap in H; simpl in H;
clear V.

rewrite <- x.
constructor.
intro i.
dependent destruction i.
unfold vcast.
generalize (lt_plus_minus_r (Gt.gt_le_S 0 1 (Lt.lt_0_Sn 0))).
intro e.
dependent destruction e.
assumption.
inversion i.

rewrite <- x.
constructor.
intro i.
dependent destruction i.
unfold vcast.
generalize (lt_plus_minus_r (Gt.gt_le_S 0 1 (Lt.lt_0_Sn 0))).
intro e.
dependent destruction e.
assumption.
inversion i.
Qed.

Lemma UD_weakly_orthogonal :
  weakly_orthogonal UD_trs.
Proof.
split.
exact UD_left_linear.
exact UD_critical_pairs_trivial.
Qed.

(* DDD... is a normal form *)
Lemma normal_form_repeat_D :
  normal_form UD_trs repeat_D.
Proof.
(* TODO: a lot of this proof is a mess, cleanup
   Also, I expect that this could be generalized and shortened quite a bit
   by using pos_eq. *)
intros [c [r [u [H1 H2]]]].
destruct H1 as [H1 | [H1 | []]].
rewrite <- H1 in *|-.
clear H1.
assert (H := (term_bis_implies_term_eq H2) (S (S (hole_depth c)))).
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
assert (H' := H First).
rewrite (peek_eq repeat_D) in H'.
dependent destruction H'.
assert (H' := H0 First).
simpl in H'.

(* idea, make [=]1 from x0 *)
assert (y0 : term_eq_up_to 1 (@Fun F X D v) (fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ varx!) (vnil fterm)))))).
(*assert (y0 : @Fun F X D v [=] fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm))))).*)
rewrite x0.
apply term_eq_up_to_refl.
clear x0.

induction c.

assert (H3 := (term_bis_implies_term_eq H2) 2).
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.
assert (H3 := H1 First).
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.

rewrite (peek_eq repeat_D) in H2.
(*intro x0.*)
assert (d : f = D).
(*assert (y1 := y0 1).*)
inversion_clear y0.
reflexivity.

(*injection x0.
intros _ d.*)
revert e H2 H y0 H0 H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v1 v2.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H y0 H0 H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
apply term_eq_implies_term_bis.
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X D (vcons (fill c (substitute u (lhs DU))) v2)) (D @ repeat_D)).
assert (jaja : fill (@CFun F X D 0 0 e v1 c v2) (substitute u (lhs DU)) = @Fun F X D (vcons (fill c (substitute u (lhs DU))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact ((term_bis_implies_term_eq H2) (S n)).
apply (@teut_fun_inv F X n D (vcons (fill c (substitute u (lhs DU))) v2) (vcons repeat_D (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
intro i.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.

clear v0 x H y0 H0 H'.
destruct c.
constructor.
constructor.
simpl.
simpl in H2.
dependent destruction H2.
assert (H3 := H First).
simpl in H3.
clear H.
rewrite (peek_eq repeat_D) in H3.
dependent destruction H3.
revert x.
dependent destruction e.
intro y.
simpl in y.
injection y.
intros _ d.
clear y x H v1 v2 v4.
revert e0.
rewrite <- d.
intro e.
constructor.
constructor.

(* almost the same argument as above for r=UD instead of r=DU *)

rewrite <- H1 in *|-.
clear H1.
assert (H := (term_bis_implies_term_eq H2) (S (hole_depth c))).
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
assert (H' := H First).
simpl in H'.
clear x.

induction c.

rewrite (peek_eq repeat_D) in H2.
inversion_clear H2.

rewrite (peek_eq repeat_D) in H2.
(*intro x0.*)
assert (d : f = D).
inversion_clear H2.
reflexivity.

revert e H2 H H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v0 v1.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
apply term_eq_implies_term_bis.
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X D (vcons (fill c (substitute u (lhs UD))) v2)) (D @ repeat_D)).
assert (jaja : fill (@CFun F X D 0 0 e v1 c v2) (substitute u (lhs UD)) = @Fun F X D (vcons (fill c (substitute u (lhs UD))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact ((term_bis_implies_term_eq H2) (S n)).
apply (@teut_fun_inv F X n D (vcons (fill c (substitute u (lhs UD))) v2) (vcons repeat_D (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
apply term_eq_up_to_weaken.
assumption.
Qed.

(* UUU... is a normal form *)
Lemma normal_form_repeat_U :
  normal_form UD_trs repeat_U.
Proof.
(* This proof is just a copy of the repeat_D proof *)
intros [c [r [u [H1 H2]]]].
destruct H1 as [H1 | [H1 | []]].

rewrite <- H1 in *|-.
clear H1.
assert (H := (term_bis_implies_term_eq H2) (S (hole_depth c))).
rewrite (peek_eq repeat_U) in H.
dependent destruction H.
assert (H' := H First).
simpl in H'.
clear x.

induction c.

rewrite (peek_eq repeat_U) in H2.
inversion_clear H2.

rewrite (peek_eq repeat_U) in H2.
(*intro x0.*)
assert (d : f = U).
inversion_clear H2.
reflexivity.

revert e H2 H H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v0 v1.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
apply term_eq_implies_term_bis.
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X U (vcons (fill c (substitute u (lhs DU))) v2)) (U @ repeat_U)).
assert (jaja : fill (@CFun F X U 0 0 e v1 c v2) (substitute u (lhs DU)) = @Fun F X U (vcons (fill c (substitute u (lhs DU))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact ((term_bis_implies_term_eq H2) (S n)).
apply (@teut_fun_inv F X n U (vcons (fill c (substitute u (lhs DU))) v2) (vcons repeat_U (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
apply term_eq_up_to_weaken.
assumption.

(* almost the same argument as above for r=DU instead of r=UD *)

rewrite <- H1 in *|-.
clear H1.
assert (H := (term_bis_implies_term_eq H2) (S (S (hole_depth c)))).
rewrite (peek_eq repeat_U) in H.
dependent destruction H.
assert (H' := H First).
rewrite (peek_eq repeat_U) in H'.
dependent destruction H'.
assert (H' := H0 First).
simpl in H'.

(* idea, make [=]1 from x0 *)
assert (y0 : term_eq_up_to 1 (@Fun F X U v) (fill c (@Fun F X U (vmap (substitute u) (vcons (D @@ varx!) (vnil fterm)))))).
(*assert (y0 : @Fun F X D v [=] fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm))))).*)
rewrite x0.
apply term_eq_up_to_refl.
clear x0.

induction c.

assert (H3 := (term_bis_implies_term_eq H2) 2).
rewrite (peek_eq repeat_U) in H3.
dependent destruction H3.
assert (H3 := H1 First).
rewrite (peek_eq repeat_U) in H3.
dependent destruction H3.

rewrite (peek_eq repeat_U) in H2.
(*intro x0.*)
assert (d : f = U).
(*assert (y1 := y0 1).*)
inversion_clear y0.
reflexivity.

(*injection x0.
intros _ d.*)
revert e H2 H y0 H0 H'.
dependent rewrite d.
intro e.
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v1 v2.
rewrite (proj1 ij).
rewrite (proj2 ij).
intros e v1 v2 H2 H y0 H0 H'.
clear f i j d ij.
apply IHc; clear IHc.

(* this part is quite ugly *)
apply term_eq_implies_term_bis.
intro n.
assert (H2' : term_eq_up_to (S n) (@Fun F X U (vcons (fill c (substitute u (lhs UD))) v2)) (U @ repeat_U)).
assert (jaja : fill (@CFun F X U 0 0 e v1 c v2) (substitute u (lhs UD)) = @Fun F X U (vcons (fill c (substitute u (lhs UD))) v2)).
dependent destruction e.
reflexivity.
rewrite jaja in H2.
exact ((term_bis_implies_term_eq H2) (S n)).
apply (@teut_fun_inv F X n U (vcons (fill c (substitute u (lhs UD))) v2) (vcons repeat_U (vnil term)) H2' First).
intro i.
apply term_eq_up_to_weaken.
apply H.
intro i.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.
dependent destruction i.
apply term_eq_up_to_weaken.
assumption.

clear v0 x H y0 H0 H'.
destruct c.
constructor.
constructor.
simpl.
simpl in H2.
dependent destruction H2.
assert (H3 := H First).
simpl in H3.
clear H.
rewrite (peek_eq repeat_U) in H3.
dependent destruction H3.
revert x.
dependent destruction e.
intro y.
simpl in y.
injection y.
intros _ d.
clear y x H v1 v2 v4.
revert e0.
rewrite <- d.
intro e.
constructor.
constructor.
Qed.

(* DDD... and UUU... are different *)
Lemma neq_repeat_D_repeat_U :
  ~ repeat_D [~] repeat_U.
Proof.
intro H.
rewrite (peek_eq repeat_D), (peek_eq repeat_U) in H.
inversion H.
Qed.

(* Reductions *)
Notation Step := (Step UD_trs).
Notation Nil' := (Nil UD_trs).

Notation "s [>] t" := (step UD_trs s t) (at level 40).
Notation "s ->> t" := (sequence UD_trs s t) (at level 40).

Notation "r [ i ]" := (pred r i) (at level 60).
Notation "r [1 i ]" := (fst (projT1 (pred r i))) (at level 60).
Notation "r [2 i ]" := (snd (projT1 (pred r i))) (at level 60).
Notation "r [seq i ]" := (fst (projT2 (pred r i))) (at level 60).
Notation "r [stp i ]" := (snd (projT2 (pred r i))) (at level 60).

Lemma DU_in :
  In DU UD_trs.
Proof.
left; reflexivity.
Qed.

Lemma UD_in :
  In UD UD_trs.
Proof.
right; left; reflexivity.
Qed.

(*
   We now build our infinite rewrite sequences.
*)

Definition sub_t t (x : X) : term := t.

(* 1) psi ->> UUU... *)

Lemma fact_term_bis_UmDSnUSnt :
  forall (m n : nat) (t : term),
    fill (Unc m (Dnc n Hole)) (substitute (sub_t (Unt n t)) (lhs DU))
    [~]
    Unt m (DnUnt (S n) t).
Proof.
intros m n t.
rewrite fill_UmDnHole_t.
unfold DnUnt.
simpl.
rewrite DDnt_eq_DnDt.
apply term_bis_Unt.
apply term_bis_Dnt.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
apply term_bis_refl.
Qed.

Lemma fact_term_eq_UmDnUnt :
  forall (m n : nat) (t : term),
    fill (Unc m (Dnc n Hole)) (substitute (sub_t (Unt n t)) (rhs DU))
    =
    Unt m (DnUnt n t).
Proof.
intros m n t.
rewrite fill_Unc_t.
rewrite fill_Dnc_t.
simpl.
reflexivity.
Qed.

Lemma fact_term_bis_UmDnUnt :
  forall (m n : nat) (t : term),
    fill (Unc m (Dnc n Hole)) (substitute (sub_t (Unt n t)) (rhs DU))
    [~]
    Unt m (DnUnt n t).
Proof.
intros m n t.
rewrite fact_term_eq_UmDnUnt.
apply term_bis_refl.
Qed.

(* Step U^m @ D^Sn @ U^Sn @ t -> U^m @ D^n @ U^n @ t *)
Definition p_UmDSnUSnt_UmDnUnt m n t : Unt m (DnUnt (S n) t) [>] Unt m (DnUnt n t) :=
  Step DU (Unc m (Dnc n Hole)) (sub_t (Unt n t)) DU_in (fact_term_bis_UmDSnUSnt m n t) (fact_term_bis_UmDnUnt m n t).

(* n-step reduction U^m @ D^n @ U^n @ t ->> U^m t *)
Fixpoint s_UmDnUnt_Umt m n t : Unt m (DnUnt n t) ->> Unt m t :=
  match n return Unt m (DnUnt n t) ->> Unt m t with
  | O   => Nil' (Unt m t)
  | S n => snoc (p_UmDSnUSnt_UmDnUnt m n t) (s_UmDnUnt_Umt m n t)
  end.

(* Is the following error a bug in Program? *)
(*
Program Definition s_Unpsin_USnpsiSn n : Unt n (psi' n) ->> Unt (S n) (psi' (S n)) :=
  s_UmDnUnt_Umt n (S (2 * n)) (U @ psi' (S n)).
Next Obligation.
symmetry.
unfold DnUnt.
rewrite psin_eq_DS2nUS2nUpsiSn.
reflexivity.
Defined.
Next Obligation.
rewrite UUnt_eq_UnUt.
reflexivity.
Defined.
*)

(* This is the ugly but working alternative to the Program above *)
Definition s_Unpsin_USnpsiSn n : Unt n (psi' n) ->> Unt (S n) (psi' (S n)).
intro n.
assert (H : Unt n (DnUnt (S (2 * n)) (U @ psi' (S n))) ->> Unt n (U @ psi' (S n))).
refine (s_UmDnUnt_Umt n (S (2 * n)) (U @ psi' (S n))).
unfold DnUnt in H.
rewrite psin_eq_DS2nUS2nUpsiSn.
simpl.
simpl in H.
unfold DnUnt.
simpl.
rewrite UUnt_eq_UnUt with n (psi' (S n)).
exact H.
Defined.

(* psi ->> U^n @ psi' n *)
Fixpoint s_psi_Unpsin n : psi ->> Unt n (psi' n) :=
  match n return psi ->> Unt n (psi' n) with
  | O   => Nil' psi
  | S n => append (s_psi_Unpsin n) (s_Unpsin_USnpsiSn n)
  end.

Lemma converges_Unpsin : converges (fun n => Unt n (psi' n)) repeat_U.
Proof.
intro d.
exists d.
intros m H.
simpl.
apply term_eq_up_to_weaken_generalized with m.
assumption.
apply term_eq_up_to_n_Unt_repeat_U.
Qed.

(* Omega-step reduction psi ->> UUU... *)
Definition s_psi_repeat_U : psi ->> repeat_U :=
  Lim s_psi_Unpsin converges_Unpsin.

(* 2) psi ->> DDD... *)

Lemma fact_term_bis_DmUSnDSnt :
  forall (m n : nat) (t : term),
    fill (Dnc m (Unc n Hole)) (substitute (sub_t (Dnt n t)) (lhs UD))
    [~]
    Dnt m (UnDnt (S n) t).
Proof.
intros m n t.
rewrite fill_DmUnHole_t.
unfold UnDnt.
simpl.
rewrite UUnt_eq_UnUt.
apply term_bis_Dnt.
apply term_bis_Unt.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
constructor.
intro i; dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
apply term_bis_refl.
Qed.

Lemma fact_term_eq_DmUnDnt :
  forall (m n : nat) (t : term),
    fill (Dnc m (Unc n Hole)) (substitute (sub_t (Dnt n t)) (rhs UD))
    =
    Dnt m (UnDnt n t).
Proof.
intros m n t.
rewrite fill_Dnc_t.
rewrite fill_Unc_t.
simpl.
reflexivity.
Qed.

Lemma fact_term_bis_DmUnDnt :
  forall (m n : nat) (t : term),
    fill (Dnc m (Unc n Hole)) (substitute (sub_t (Dnt n t)) (rhs UD))
    [~]
    Dnt m (UnDnt n t).
Proof.
intros m n t.
rewrite fact_term_eq_DmUnDnt.
apply term_bis_refl.
Qed.

(* Step D^m @ U^Sn @ D^Sn @ t -> D^m @ U^n @ D^n @ t *)
Definition p_DmUSnDSnt_DmUnDnt m n t : Dnt m (UnDnt (S n) t) [>] Dnt m (UnDnt n t) :=
  Step UD (Dnc m (Unc n Hole)) (sub_t (Dnt n t)) UD_in (fact_term_bis_DmUSnDSnt m n t) (fact_term_bis_DmUnDnt m n t).

(* n-step reduction D^m @ U^n @ D^n @ t ->> D^m t *)
Fixpoint s_DmUnDnt_Dmt m n t : Dnt m (UnDnt n t) ->> Dnt m t :=
  match n return Dnt m (UnDnt n t) ->> Dnt m t with
  | O   => Nil' (Dnt m t)
  | S n => snoc (p_DmUSnDSnt_DmUnDnt m n t) (s_DmUnDnt_Dmt m n t)
  end.

(* Is the following error a bug in Program? *)
(*
Program Definition s_DnU2npsin_DSnU2SnpsiSn n : Dnt n (Unt (2 * n) (psi' n)) ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n))) :=
  s_DmUnDnt_Dmt n (2 * n) (D @ (Unt (2 * (S n)) (psi' (S n)))).
Next Obligation.
symmetry.
unfold UnDnt.
rewrite psin_eq_DS2nUS2nUpsiSn.
unfold DnUnt.
simpl.
rewrite DDnt_eq_DnDt.
rewrite <- plus_n_Sm.
rewrite <- UUnt_eq_UnUt.
reflexivity.
Defined.
Next Obligation.
rewrite DDnt_eq_DnDt.
reflexivity.
Defined.
*)

(* This is the ugly but working alternative to the Program above *)
Definition s_DnU2npsin_DSnU2SnpsiSn n : Dnt n (Unt (2 * n) (psi' n)) ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n))).
intro n.
assert (H : Dnt n (UnDnt (2 * n) (D @ Unt (2 * (S n)) (psi' (S n)))) ->> Dnt n (D @ (Unt (2 * S n)) (psi' (S n)))).
refine (s_DmUnDnt_Dmt n (2 * n) (D @ (Unt (2 * (S n)) (psi' (S n))))).
unfold UnDnt in H.
rewrite psin_eq_DS2nUS2nUpsiSn.
unfold DnUnt.
simpl.
rewrite DDnt_eq_DnDt.
simpl in H.
rewrite <- plus_n_Sm in H.
rewrite <- plus_n_Sm.
simpl in H.
simpl.
(*pattern (U @ Unt (n + (n + 0)) (psi' (S n))) at 1 in H.*)
rewrite <- UUnt_eq_UnUt.
rewrite DDnt_eq_DnDt.
exact H.
Defined.

(* psi ->> D^n @ U^2n @ psi' n *)
(*
Fixpoint s_psi_DnU2npsin n : psi ->> Dnt n (Unt (2 * n) (psi' n)) :=
  match n return psi ->> Dnt n (Unt (2 * n) (psi' n)) with
  | O   => Nil' psi
  | S n => append (s_psi_DnU2npsin n) (s_DnU2npsin_DSnU2SnpsiSn n)
  end.
*)
Fixpoint s_psi_DSnU2SnpsiSn n : psi ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n))) :=
  match n return psi ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n))) with
  | O   => s_DnU2npsin_DSnU2SnpsiSn 0
  | S n => append (s_psi_DSnU2SnpsiSn n) (s_DnU2npsin_DSnU2SnpsiSn (S n))
  end.

Lemma converges_DSnU2SnpsiSn : converges (fun n => Dnt (S n) (Unt (2 * (S n)) (psi' (S n)))) repeat_D.
Proof.
intro d.
exists d.
intros m H.
simpl.
apply term_eq_up_to_weaken_generalized with m.
assumption.
rewrite DDnt_eq_DnDt.
apply term_eq_up_to_n_Dnt_repeat_D.
Qed.

(* Omega-step reduction psi ->> DDD... *)
Definition s_psi_repeat_D : psi ->> repeat_D :=
  Lim s_psi_DSnU2SnpsiSn converges_DSnU2SnpsiSn.

(*
   It should be noted that at this point, nothing has been said yet about
   well-formedness of the rewrite sequences. Furthermore, it might not
   converge.

   So we proceed by proving the 'wf' property. Convergence seems our of
   our reach at this point unfortunately.
*)

Lemma finite_s_UmDnUnt_Umt :
  forall m n t, finite (s_UmDnUnt_Umt m n t).
Proof.
induction n as [| n IH]; intro t; simpl.
exact I.
apply snoc_finite.
apply IH.
Qed.

Lemma finite_s_Unpsin_USnpsiSn :
  forall n, finite (s_Unpsin_USnpsiSn n).
Proof.
intro n.
unfold s_Unpsin_USnpsiSn; simpl.
(* http://www.lix.polytechnique.fr/coq/stdlib/Coq.Program.Equality.html *)
unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
apply finite_s_UmDnUnt_Umt.
Qed.

Lemma finite_s_psi_Unpsin :
  forall n : nat, finite (s_psi_Unpsin n).
Proof.
induction n as [| n IH]; simpl.
exact I.
apply append_finite.
exact IH.
apply finite_s_Unpsin_USnpsiSn.
Qed.

Lemma finite_s_DmUnDnt_Dmt :
  forall m n t, finite (s_DmUnDnt_Dmt m n t).
Proof.
induction n as [| n IH]; intro t; simpl.
exact I.
apply snoc_finite.
apply IH.
Qed.

(* it is very unclear to me why we have to take this statement apart *)
Lemma bleh :
  forall n,
       finite
     (eq_rect
        (Dnt (n + (n + 0)) (D @ U @ Unt (n + (n + 0)) (U @ psi' (S n))))
        (fun y : term =>
         Dnt n (Unt (n + (n + 0)) y) ->>
         Dnt n (D @ U @ U @ Unt (n + (n + 0)) (psi' (S n))))
        (eq_rect (U @ Unt (n + (n + 0)) (psi' (S n)))
           (fun t : term =>
            Dnt n (Unt (n + (n + 0)) (Dnt (n + (n + 0)) (D @ U @ t))) ->>
            Dnt n (D @ U @ U @ Unt (n + (n + 0)) (psi' (S n))))
           (s_DmUnDnt_Dmt n (n + (n + 0))
              (D @ U @ U @ Unt (n + (n + 0)) (psi' (S n))))
           (Unt (n + (n + 0)) (U @ psi' (S n)))
           (UUnt_eq_UnUt (n + (n + 0)) (psi' (S n))))
        (D @ Dnt (n + (n + 0)) (U @ Unt (n + (n + 0)) (U @ psi' (S n))))
        (eq_sym
           (DDnt_eq_DnDt (n + (n + 0))
              (U @ Unt (n + (n + 0)) (U @ psi' (S n)))))).
Proof.
intro n.
repeat (elim_eq_rect ; simpl).
apply finite_s_DmUnDnt_Dmt.
Qed.

Lemma finite_s_DnU2npsin_DSnU2SnpsiSn :
  forall n, finite (s_DnU2npsin_DSnU2SnpsiSn n).
Proof.
intro n.
unfold s_DnU2npsin_DSnU2SnpsiSn; simpl.
unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
apply bleh.
Qed.

(* it is very unclear to me why we have to take this statement apart *)
Lemma blegh :
   finite
     (eq_rect (DnUnt 1 (U @ psi' 1))
        (fun y : term => y ->> (D @ U @ U @ psi' 1))
        (Nil' (D @ U @ U @ psi' 1)) (psi' 0) (eq_sym (psin_eq_DS2nUS2nUpsiSn 0))).
Proof.
elim_eq_rect; simpl.
exact I.
Qed.

Lemma finite_s_psi_DSnU2SnpsiSn :
  forall n : nat, finite (s_psi_DSnU2SnpsiSn n).
Proof.
induction n as [| n IH]; simpl.
unfold s_DnU2npsin_DSnU2SnpsiSn; simpl.
unfold eq_rect_r; repeat (elim_eq_rect; simpl); apply blegh.
apply append_finite.
exact IH.
exact (finite_s_DnU2npsin_DSnU2SnpsiSn (S n)).
Qed.

Lemma s_UmDnUnt_Umt_is_cons :
  forall m n t,
    exists s, exists r : _ ->> s, exists p : s [>] _,
      s_UmDnUnt_Umt m (S n) t = Cons r p.
Proof.
induction n; intro t; simpl.
exists (Unt m (DnUnt 1 t)).
exists (Nil' (Unt m (DnUnt 1 t))).
exists (p_UmDSnUSnt_UmDnUnt m 0 t).
reflexivity.
simpl in IHn.
specialize IHn with t.
destruct IHn as [s [r [p IH]]].
rewrite IH.
simpl.
exists s.
exists (snoc (p_UmDSnUSnt_UmDnUnt m (S n) t) r).
exists p.
reflexivity.
Qed.

Lemma plus_SnO :
  forall n,
    n + S (n + 0) = S (n + n).
Proof.
intro n.
rewrite <- plus_n_O.
rewrite plus_n_Sm.
reflexivity.
Qed.

Lemma embed_strict_append_Unpsin_USnpsiSn :
  forall t n (r : t ->> Unt n (psi' n)),
    embed_strict r (append r (s_Unpsin_USnpsiSn n)).
Proof.
intro t.
destruct n as [| n]; simpl;
unfold s_Unpsin_USnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl); intro r.
exists (inl _ tt).
apply embed_refl.
revert r.
rewrite (plus_SnO n).
intro r.
destruct (s_UmDnUnt_Umt_is_cons (S n) (n + n) (U @ psi' (S (S n)))) as [s [q [p H]]].
rewrite H.
exists (inl _ tt).
simpl.
apply embed_append_right.
Qed.

Lemma wf_s_psi_Unpsin :
  forall n : nat, wf (s_psi_Unpsin n).
Proof.
intro n.
apply wf_finite.
apply finite_s_psi_Unpsin.
Qed.

(* This reduction is well-formed *)
Lemma wf_s_psi_repeat_U :
  wf s_psi_repeat_U.
Proof.
split.
apply wf_s_psi_Unpsin.
intros n m H.
induction H; simpl.
apply embed_strict_append_Unpsin_USnpsiSn.
apply embed_strict_trans with psi (Unt m (psi' m)) (s_psi_Unpsin m).
apply IHle.
apply embed_strict_append_Unpsin_USnpsiSn.
Qed.

Lemma s_DmUnDnt_Dmt_is_cons :
  forall m n t,
    exists s, exists r : _ ->> s, exists p : s [>] _,
      s_DmUnDnt_Dmt m (S n) t = Cons r p.
Proof.
induction n; intro t; simpl.
exists (Dnt m (UnDnt 1 t)).
exists (Nil' (Dnt m (UnDnt 1 t))).
exists (p_DmUSnDSnt_DmUnDnt m 0 t).
reflexivity.
simpl in IHn.
specialize IHn with t.
destruct IHn as [s [r [p IH]]].
rewrite IH.
simpl.
exists s.
exists (snoc (p_DmUSnDSnt_DmUnDnt m (S n) t) r).
exists p.
reflexivity.
Qed.

Program Definition aa : (D @ U @ U @ psi' 1) ->> Dnt 1 (UnDnt 1 (D @ Unt 4 (psi' 2))) :=
  Cons (Nil' (Dnt 1 (UnDnt 2 (D @ (Unt 4 (psi' 2)))))) (p_DmUSnDSnt_DmUnDnt 1 1 (D @ (Unt 4 (psi' 2)))).
Next Obligation.
assert (e := (psin_eq_DS2nUS2nUpsiSn 1)).
unfold DnUnt in e.
simpl in e.
rewrite e.
unfold UnDnt.
simpl.
reflexivity.
Defined.

Lemma s_DnU2npsin_DSnU2SnpsiSn_is_cons :
  forall n,
    exists s, exists r : _ ->> s, exists p : s [>] _,
      s_DnU2npsin_DSnU2SnpsiSn (S n) = Cons r p.
Proof.
induction n; simpl.
exists (Dnt 1 (UnDnt 1 (D @ (Unt 4 (psi' 2))))).
exists aa.
exists (p_DmUSnDSnt_DmUnDnt 1 0 (D @ (Unt 4 (psi' 2)))).
simpl.
unfold s_DnU2npsin_DSnU2SnpsiSn.
unfold aa.
simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
(*
exists (Cons (Nil' (Dnt 1 (UnDnt 2 (D @ (Unt 4 (psi' 2)))))) (p_DmUSnDSnt_DmUnDnt 1 1 (D @ (Unt 4 (psi' 2))))).
exists (p_DmUSnDSnt_DmUnDnt 1 0 (D @ (Unt 4 (psi' 2)))).
unfold s_DnU2npsin_DSnU2SnpsiSn.
simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
*)
Admitted.

Lemma plus_SSnO :
  forall n,
    n + S (S (n + 0)) = S (S (n + n)).
Proof.
intro n.
rewrite <- plus_n_O.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
reflexivity.
Qed.

Lemma embed_strict_append_DnU2npsin_DSnU2SnpsiSn :
  forall t n (r : t ->> Dnt (S n) (Unt (2 * (S n)) (psi' (S n)))),
    embed_strict r (append r (s_DnU2npsin_DSnU2SnpsiSn (S n))).
Proof.
intros t.
destruct n as [| n].
unfold s_DnU2npsin_DSnU2SnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl); intro r.
exists (inl _ tt).
simpl.
apply embed_cons_right.
apply embed_refl.

generalize (S n).
clear n.
intro n.
unfold s_DnU2npsin_DSnU2SnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl); intro r.

(*
intro t.
induction n as [| n IH]; simpl;
unfold s_DnU2npsin_DSnU2SnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl); intro r.
exists (inl _ tt).
simpl.
apply embed_cons_right.
apply embed_refl.
(*revert r.
rewrite (plus_SSnO n).
intro r.*)




destruct (s_DmUnDnt_Dmt_is_cons (S (S n)) (S (n + n)) (D @ U @ U @ U @ (Unt (n + S (S (S (n + 0)))) (psi' (S (S (S n))))))) as [s [q [p H]]].
rewrite <- (plus_SSnO n) in H.
rewrite H.
exists (inl _ tt).
simpl.
apply embed_append_right.
*)
Admitted.

Lemma wf_s_psi_DSnU2SnpsiSn :
  forall n : nat, wf (s_psi_DSnU2SnpsiSn n).
Proof.
intro n.
apply wf_finite.
apply finite_s_psi_DSnU2SnpsiSn.
Qed.

(* This reduction is well-formed *)
Lemma wf_s_psi_repeat_D :
  wf s_psi_repeat_D.
Proof.
split.
apply wf_s_psi_DSnU2SnpsiSn.
intros n m H.
induction H; simpl.
apply embed_strict_append_DnU2npsin_DSnU2SnpsiSn.
apply embed_strict_trans with psi (Dnt m (Unt (2 * m) (psi' m))) (s_psi_DnU2npsin m).
apply IHle.
apply embed_strict_append_DnU2npsin_DSnUS2npsiSn.
Qed.

Lemma UD_no_unique_normal_forms :
  ~ unique_normal_forms UD_trs.
Proof.
intro H.
apply neq_repeat_D_repeat_U.
apply H with psi s_psi_repeat_D s_psi_repeat_U.
exact wf_s_psi_repeat_D.
exact wf_s_psi_repeat_U.
exact normal_form_repeat_D.
exact normal_form_repeat_U.
Qed.

Lemma unwo :
  ~ forall F X trs, weakly_orthogonal (F := F) (X := X) trs -> unique_normal_forms trs.
Proof.
intro H.
apply UD_no_unique_normal_forms.
apply H.
apply UD_weakly_orthogonal.
Qed.
