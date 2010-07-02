Require Import Rewriting.
Require Import Equality.

Set Implicit Arguments.

(*
  We construct the weakly orthogonal TRS with rules

    PS : P(S(x)) -> x
    SP : S(P(x)) -> x

  and show it is a counterexample to UN-inf.

  Because we have X for variables, we use D and U instead of P and S.
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

Definition variable : Set := nat.

Fixpoint beq_var (x y : variable) : bool :=
  match x, y with
  | 0, 0       => true
  | S x', S y' => beq_var x' y'
  | _,    _    => false
end.

Lemma beq_var_ok : forall x y, beq_var x y = true <-> x = y.
Proof.
induction x as [|x IH]; destruct y;
  simpl; split; intro H; try (reflexivity || discriminate).
  f_equal. exact (proj1 (IH _) H).
  apply (proj2 (IH _)). inversion H. reflexivity.
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

Notation id_sub := (empty_substitution F X).

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

Lemma fill_UmDnc_t :
  forall m n c t,
    fill (Unc m (Dnc n c)) t = Unt m (Dnt n (fill c t)).
Proof.
intros m n c t.
rewrite fill_Unc_t.
rewrite fill_Dnc_t.
reflexivity.
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

(* D(U(x)) -> x *)
Definition DU_l : fterm := D @@ U @@ 1!.
Definition DU_r : fterm := 1!.

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

(* U(D(x)) -> x *)
Definition UD_l : fterm := U @@ D @@ 1!.
Definition UD_r : fterm := 1!.

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

Definition UNWO_trs : trs := DU :: UD :: nil.

Lemma UNWO_left_linear :
  trs_left_linear UNWO_trs.
Proof.
split; [| split];
  unfold left_linear; unfold linear; simpl;
    constructor.
intro; assumption.
constructor.
intro; assumption.
constructor.
Qed.

Implicit Arguments critical_pair [F X system].

Lemma cp_U : critical_pair (system := UNWO_trs) (U @@ 1!) (U @@ 1!).
Proof.
unfold critical_pair.
exists UD.
exists DU.
exists (0 :: nil).
exists (fun n => match n with 1 => U @@ 1! | _ => n! end).
exists id_sub.
split.
right; left; reflexivity.
split.
left; reflexivity.
split.
discriminate.
split.
reflexivity.
split.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
constructor.
intro i.
dependent destruction i.
apply term_bis_refl.
inversion i.
inversion i.
split.
constructor.
intro i.
dependent destruction i.
simpl.
unfold vmap.
simpl.
unfold vcast.
generalize (lt_plus_minus_r (Gt.gt_le_S 0 1 (Lt.lt_0_Sn 0))).
intro e.
dependent destruction e.
simpl.
constructor.
inversion i.
apply term_bis_refl.
Qed.

Lemma cp_trivial :
  forall t1 t2,
    critical_pair (system := UNWO_trs) t1 t2 ->
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

(* TODO: prove UNWO_trs weakly orthogonal *)

(* DDD... is infinite *)
Lemma infinite_D :
  infinite repeat_D.
Proof.
intro d.
assert (S : exists p : position, position_depth p = d /\ subterm repeat_D p = Some repeat_D).
exists ((fix z n := match n with O => nil | S n => 0 :: (z n) end) d).
induction d; split.
reflexivity.
reflexivity.
simpl.
f_equal.
apply IHd.
simpl.
apply IHd.
destruct S as [p S].
exists p.
split.
apply S.
rewrite (proj2 S).
discriminate.
Qed.

(* UUU... is infinite *)
Lemma infinite_U :
  infinite repeat_U.
Proof.
intro d.
assert (S : exists p : position, position_depth p = d /\ subterm repeat_U p = Some repeat_U).
exists ((fix z n := match n with O => nil | S n => 0 :: (z n) end) d).
induction d; split.
reflexivity.
reflexivity.
simpl.
f_equal.
apply IHd.
simpl.
apply IHd.
destruct S as [p S].
exists p.
split.
apply S.
rewrite (proj2 S).
discriminate.
Qed.

(* DDD... is infinite *)
(* This uses the (alternative) coinductive term_inf predicate *)
Lemma term_inf_D :
  term_inf repeat_D.
Proof.
cofix co.
rewrite (peek_eq repeat_D); simpl.
apply Fun_inf with (First (n := 0)).
assumption.
Qed.

(* UUU... is infinite *)
(* This uses the (alternative) coinductive term_inf predicate *)
Lemma term_inf_U :
  term_inf repeat_U.
Proof.
cofix co.
rewrite (peek_eq repeat_U); simpl.
apply Fun_inf with (First (n := 0)).
assumption.
Qed.

(* DDD... is a normal form *)
Lemma nf_D :
  normal_form (system := UNWO_trs) repeat_D.
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
assert (y0 : term_eq_up_to 1 (@Fun F X D v) (fill c (@Fun F X D (vmap (substitute u) (vcons (U @@ 1 !) (vnil fterm)))))).
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
Lemma nf_U :
  normal_form (system := UNWO_trs) repeat_U.
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
assert (y0 : term_eq_up_to 1 (@Fun F X U v) (fill c (@Fun F X U (vmap (substitute u) (vcons (D @@ 1 !) (vnil fterm)))))).
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

(* DDD... is an infinite normal form *)
Lemma infinite_nf_D :
  infinite repeat_D /\ normal_form (system := UNWO_trs) repeat_D.
Proof.
exact (conj infinite_D nf_D).
Qed.

(* UUU... is an infinite normal form *)
Lemma infinite_nf_U :
  infinite repeat_U /\ normal_form (system := UNWO_trs) repeat_U.
Proof.
exact (conj infinite_U nf_U).
Qed.

(* DDD... and UUU... are different *)
Lemma neq_D_U :
  ~ repeat_D [~] repeat_U.
Proof.
intro H.
rewrite (peek_eq repeat_D), (peek_eq repeat_U) in H.
inversion H.
Qed.

(* DDD... and UUU... are the only infinite normal forms *)
(* TODO: this is a very ugly proof *)
Lemma only_infinite_nf_D_U :
  forall t,
    infinite t /\ normal_form (system := UNWO_trs) t ->
    t [~] repeat_D \/ t [~] repeat_U.
Proof.
intros [x | [] args] [It Nt].

destruct (It 1) as [p [Dp Hp]].
contradict Hp.
destruct p as [| a [| b p]].
discriminate Dp.
reflexivity.
discriminate Dp.

left.
assert (H : term_eq_up_to 1 (@Fun F X D args) repeat_D).
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
constructor.
apply term_eq_implies_term_bis.
intro n.
generalize dependent (@Fun F X D args).
induction n as [| n IH]; intros t It Nt H.
constructor.
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
clear H.
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.

apply IH; clear IH.
intro d.
assert (H := It (S d)).
destruct H as [p [H1 H2]].
dependent destruction p.
exists p.
split.
reflexivity.
destruct n0.
assumption.
contradict H2.
reflexivity.

intros [c [r [u [H1 H2]]]].
apply Nt.
exists (D @@@ c).
exists r.
exists u.
split.
assumption.
simpl.
constructor.
intro i.
dependent destruction i.
assumption.
inversion i.

(* contradict this with Nt *)
assert (Hx : ~ exists w, v First = @Fun F X U w).
intro Hx.
unfold normal_form in Nt.
apply Nt.
clear It Nt. (* readability *)
destruct Hx as [w H].
exists Hole.
exists DU.
exists (fun n => w First).
split.
left; reflexivity.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
rewrite H.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
apply term_bis_refl.
inversion i.
inversion i.
clear Nt.

unfold infinite in It.
specialize It with 2.
destruct It as [p [H1 H2]].
destruct p as [| [| a] [| b [| c p]]].
inversion H1.
inversion H1.
simpl in H2.
unfold vhead in H2.
destruct (v First).
contradict H2.
reflexivity.
destruct f.
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
constructor.
contradict Hx.
exists v0.
reflexivity.
inversion H1.
inversion H1.
contradict H2.
reflexivity.
inversion H1.
inversion i.

(* Same argument follows *)

right.
assert (H : term_eq_up_to 1 (@Fun F X U args) repeat_U).
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
constructor.
apply term_eq_implies_term_bis.
intro n.
generalize dependent (@Fun F X U args).
induction n as [| n IH]; intros t It Nt H.
constructor.
rewrite (peek_eq repeat_U) in H.
dependent destruction H.
clear H.
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.

apply IH; clear IH.
intro d.
assert (H := It (S d)).
destruct H as [p [H1 H2]].
dependent destruction p.
exists p.
split.
reflexivity.
destruct n0.
assumption.
contradict H2.
reflexivity.

intros [c [r [u [H1 H2]]]].
apply Nt.
exists (U @@@ c).
exists r.
exists u.
split.
assumption.
simpl.
constructor.
intro i.
dependent destruction i.
assumption.
inversion i.

(* contradict this with Nt *)
assert (Hx : ~ exists w, v First = @Fun F X D w).
intro Hx.
unfold normal_form in Nt.
apply Nt.
clear It Nt. (* readability *)
destruct Hx as [w H].
exists Hole.
exists UD.
exists (fun n => w First).
split.
right; left; reflexivity.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
rewrite H.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
apply term_bis_refl.
inversion i.
inversion i.
clear Nt.

unfold infinite in It.
specialize It with 2.
destruct It as [p [H1 H2]].
destruct p as [| [| a] [| b [| c p]]].
inversion H1.
inversion H1.
simpl in H2.
unfold vhead in H2.
destruct (v First).
contradict H2.
reflexivity.
destruct f.
contradict Hx.
exists v0.
reflexivity.
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
constructor.
inversion H1.
inversion H1.
contradict H2.
reflexivity.
inversion H1.
inversion i.
Qed.

(* DDD... and UUU... are the only infinite normal forms *)
(* This is alternative, using coinductive term_inf predicate *)
(* TODO: this is a very ugly proof *)
Lemma only_term_inf_nf_D_U :
  forall t,
    term_inf t /\ normal_form (system := UNWO_trs) t ->
    t [~] repeat_D \/ t [~] repeat_U.
Proof.
intros [x | [] args] [It Nt].

inversion It.

left.
assert (H : term_eq_up_to 1 (@Fun F X D args) repeat_D).
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
constructor.
apply term_eq_implies_term_bis.
intro n.
generalize dependent (@Fun F X D args).
induction n as [| n IH]; intros t It Nt H.
constructor.
rewrite (peek_eq repeat_D) in H.
dependent destruction H.
clear H.
rewrite (peek_eq repeat_D).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.

apply IH; clear IH.
inversion It.
dependent destruction H1.
revert H0.
dependent destruction i.
trivial.
inversion i.

intros [c [r [u [H1 H2]]]].
apply Nt.
exists (D @@@ c).
exists r.
exists u.
split.
assumption.
simpl.
constructor.
intro i.
dependent destruction i.
assumption.
inversion i.

(* contradict this with Nt *)
assert (Hx : ~ exists w, v First = @Fun F X U w).
intro Hx.
unfold normal_form in Nt.
apply Nt.
clear It Nt. (* readability *)
destruct Hx as [w H].
exists Hole.
exists DU.
exists (fun n => w First).
split.
left; reflexivity.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
rewrite H.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
apply term_bis_refl.
inversion i.
inversion i.
clear Nt.

inversion It.
clear It.
dependent destruction H1.
revert H0.
dependent destruction i.
intro It.
destruct (v First).
inversion It.
destruct f.
rewrite (peek_eq repeat_D); simpl.
constructor.
constructor.
contradict Hx.
exists v0.
reflexivity.
inversion i.
inversion i.

(* Same argument follows *)

right.
assert (H : term_eq_up_to 1 (@Fun F X U args) repeat_U).
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
constructor.
apply term_eq_implies_term_bis.
intro n.
generalize dependent (@Fun F X U args).
induction n as [| n IH]; intros t It Nt H.
constructor.
rewrite (peek_eq repeat_U) in H.
dependent destruction H.
clear H.
rewrite (peek_eq repeat_U).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.

apply IH; clear IH.
inversion It.
dependent destruction H1.
revert H0.
dependent destruction i.
trivial.
inversion i.

intros [c [r [u [H1 H2]]]].
apply Nt.
exists (U @@@ c).
exists r.
exists u.
split.
assumption.
simpl.
constructor.
intro i.
dependent destruction i.
assumption.
inversion i.

(* contradict this with Nt *)
assert (Hx : ~ exists w, v First = @Fun F X D w).
intro Hx.
unfold normal_form in Nt.
apply Nt.
clear It Nt. (* readability *)
destruct Hx as [w H].
exists Hole.
exists UD.
exists (fun n => w First).
split.
right; left; reflexivity.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
rewrite H.
simpl.
constructor.
intro i.
dependent destruction i.
unfold vmap.
simpl.
apply term_bis_refl.
inversion i.
inversion i.
clear Nt.

inversion It.
clear It.
dependent destruction H1.
revert H0.
dependent destruction i.
intro It.
destruct (v First).
inversion It.
destruct f.
contradict Hx.
exists v0.
reflexivity.
rewrite (peek_eq repeat_U); simpl.
constructor.
constructor.
inversion i.
inversion i.
Qed.

(* Reductions *)
Notation Step := (Step UNWO_trs).
Notation Nil' := (Nil UNWO_trs).

Notation "s [>] t" := (step UNWO_trs s t) (at level 40).
Notation "s ->> t" := (sequence UNWO_trs s t) (at level 40).

Notation "r [ i ]" := (pred r i) (at level 60).
Notation "r [1 i ]" := (fst (projT1 (pred r i))) (at level 60).
Notation "r [2 i ]" := (snd (projT1 (pred r i))) (at level 60).
Notation "r [seq i ]" := (fst (projT2 (pred r i))) (at level 60).
Notation "r [stp i ]" := (snd (projT2 (pred r i))) (at level 60).

Lemma DU_in :
  In DU UNWO_trs.
Proof.
left; reflexivity.
Qed.

Lemma UD_in :
  In UD UNWO_trs.
Proof.
right; left; reflexivity.
Qed.

(* DUDU... rewrites only to itself *)
(* TODO: we don't really need this *)
Lemma rewrites_to_itself_DU :
  forall t (p : repeat_DU [>] t),
    t [~] repeat_DU.
Proof.
intros s p.
dependent destruction p.
destruct i as [H | [H | []]]; try (rewrite <- H in t1, t0; clear H).

unfold DU, lhs, DU_l in t0.
unfold DU, rhs, DU_r in t1.
apply term_bis_trans with (fill c (substitute u (1 !))).
exact (term_bis_symm t1).
clear t1.

assert ((substitute u (D @@ U @@ 1!)) [~] repeat_DU).
induction c using context_ind2; simpl in t0.
assumption.

(* absurd case *)
rewrite (peek_eq repeat_DU) in t0.
simpl in t0.
dependent destruction t0.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
dependent destruction H.

apply IHc; clear IHc.
rewrite (peek_eq repeat_DU) in t0.
simpl in t0.
dependent destruction t0.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
dependent destruction H.
specialize H with (First (n := 0)).
simpl in H.
assert (nm : n = 0 /\ m = 0).
destruct n as [| [| n]]; auto; discriminate a.
revert a x z H.
rewrite (proj1 nm).
rewrite (proj2 nm).
simpl.
intro a.
clear n m nm.
dependent destruction a.
simpl.
intros x z H.
assumption.

assert (substitute u (1 !) [~] repeat_DU).
dependent destruction H.
specialize H with (First (n := 0)).
unfold vmap in H.
simpl in H.
dependent destruction H.
specialize H with (First (n := 0)).
unfold vmap in H.
simpl in H.
rewrite (peek_eq repeat_DU) in x0.
dependent destruction x0.
assumption.

assert (substitute u (D @@ U @@ 1 !) [~] substitute u (1 !)).
apply term_bis_trans with repeat_DU.
assumption.
apply term_bis_symm.
assumption.
clear H H0.

(* TODO: This should be a separate lemma *)
generalize dependent (substitute u (1 !)).
generalize dependent (substitute u (D @@ U @@ 1 !)).
generalize dependent repeat_DU.
clear t r u.

induction c as [| [] i j e v c IH w]; intros s t H1 u H2; simpl in H1.
apply term_bis_trans with t.
apply term_bis_symm.
assumption.
assumption.

dependent destruction H1.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
constructor.
intro i.
dependent destruction i.
simpl.
apply IH with t.
assumption.
assumption.
inversion i.

dependent destruction H1.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
constructor.
intro i.
dependent destruction i.
simpl.
apply IH with t.
assumption.
assumption.
inversion i.

(* This case is the same as the previous *)

unfold UD, lhs, UD_l in t0.
unfold UD, rhs, UD_r in t1.
apply term_bis_trans with (fill c (substitute u (1 !))).
exact (term_bis_symm t1).
clear t1.

destruct c; simpl in t0 |- *; rewrite (peek_eq repeat_DU) in t0; simpl in t0;
dependent destruction t0.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v v0 H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v v0 H.
clear v.

change (fill c (substitute u (U @@ D @@ 1!)) [~] (U @ repeat_DU)) in H.
assert ((substitute u (U @@ D @@ 1!)) [~] (U @ repeat_DU)).
induction c using context_ind2; simpl in H.
assumption.

(* absurd case *)
dependent destruction H.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
rewrite (peek_eq repeat_DU) in H.
simpl in H.
dependent destruction H.

apply IHc; clear IHc.
rewrite (peek_eq repeat_DU) in H.
simpl in H.
dependent destruction H.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
dependent destruction H.
specialize H with (First (n := 0)).
simpl in H.
assert (nm : n = 0 /\ m = 0).
destruct n as [| [| n]]; auto; discriminate a.
revert a x z H.
rewrite (proj1 nm).
rewrite (proj2 nm).
simpl.
intro a.
clear n m nm.
dependent destruction a.
simpl.
intros x z H.
assumption.

assert (substitute u (1 !) [~] (U @ repeat_DU)).
dependent destruction H0.
specialize H0 with (First (n := 0)).
unfold vmap in H0.
simpl in H.
dependent destruction H0.
specialize H0 with (First (n := 0)).
unfold vmap in H0.
simpl in H0.
rewrite (peek_eq repeat_DU) in x.
dependent destruction x.
assumption.

assert (substitute u (U @@ D @@ 1 !) [~] substitute u (1 !)).
apply term_bis_trans with (U @ repeat_DU).
assumption.
apply term_bis_symm.
assumption.
clear H0 H1.

rewrite (peek_eq (repeat_DU)).
simpl.
constructor.
intro i.
dependent destruction i.
simpl.
clear v0.
change (fill c (substitute u (1 !)) [~] (U @ repeat_DU)).

(* TODO: This should be a separate lemma *)
generalize dependent (substitute u (1 !)).
generalize dependent (substitute u (U @@ D @@ 1 !)).
generalize dependent (U @ repeat_DU).
clear t r u.

induction c as [| [] i j e v c IH w]; intros s t H1 u H2; simpl in H1.
apply term_bis_trans with t.
apply term_bis_symm.
assumption.
assumption.

dependent destruction H1.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
constructor.
intro i.
dependent destruction i.
simpl.
apply IH with t.
assumption.
assumption.
inversion i.

dependent destruction H1.
specialize H with (First (n := 0)).
assert (ij : i = 0 /\ j = 0).
destruct i as [| [| i]]; auto; discriminate e.
revert e v w H.
rewrite (proj1 ij).
rewrite (proj2 ij).
simpl.
intro e.
clear i j ij.
dependent destruction e.
simpl.
intros v w H.
constructor.
intro i.
dependent destruction i.
simpl.
apply IH with t.
assumption.
assumption.
inversion i.
inversion i.
Qed.

(* Zero-step reduction psi ->> psi *)
Definition s_psi_psi : psi ->> psi := Nil' psi.

(* Substitution for step psi -> U @ psi' 1 *)
Definition sub_psi_Upsi1 (x : X) : term :=
  match x with
  | 1 => U @ psi' 1
  | _ => Var x
  end.

Lemma fact_term_bis_psi :
  fill Hole (substitute sub_psi_Upsi1 (lhs DU)) [~] psi.
Proof.
rewrite (peek_eq psi).
simpl.
constructor.
intro i; simpl in i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
(* this is really annoying, but i guess there's no way around it... *)
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => psi' 1
      | S u0 => U @ U @ U2nt u0
      end) 1)).
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => psi' 1
       | S u0 => U @ U @ U2nt u0
       end) 0)).
simpl.
constructor.
unfold vmap.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq (psi' 1)).
apply term_bis_refl.
Qed.

(* Step psi -> U @ psi' 1 *)
Definition p_psi_Upsi1 : psi [>] (U @ psi' 1) :=
  Step DU Hole sub_psi_Upsi1 DU_in fact_term_bis_psi (term_bis_refl (U @ psi' 1)).

(* Single-step reduction psi ->> U @ psi' 1 *)
Definition s_psi_Upsi1 : psi ->> (U @ psi' 1) :=
  Cons s_psi_psi p_psi_Upsi1.

(* Substitution for step U @ psi' 1 -> U D D U U U @ psi' 2 *)
Definition sub_Upsi1_UDDUUUpsi2 (x : X) : term :=
  match x with
  | 1 => U @ U @ U @ psi' 2
  | _ => Var x
  end.

Lemma fact_term_bis_Upsi1 :
  fill (U @@@ D @@@ D @@@ Hole) (substitute sub_Upsi1_UDDUUUpsi2 (lhs DU))
  [~]
  (U @ psi' 1).
Proof.
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
rewrite (peek_eq (psi' 1)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
       match d with
       | 0 =>
           D @
           (cofix U2nt (u : nat) : term :=
              match u with
              | 0 => psi' 2
              | S u0 => U @ U @ U2nt u0
              end) 2
       | S d0 => D @ D @ D2nDt d0
       end) 0)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => psi' 2
      | S u0 => U @ U @ U2nt u0
      end) 2)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
      match u with
      | 0 => psi' 2
      | S u0 => U @ U @ U2nt u0
      end) 1)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
generalize (psi' 2).
intro t.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) 0)).
simpl.
destruct t; apply term_bis_U; apply term_bis_refl.
Qed.

(* Step U @ psi' 1 -> U D D U U U @ psi' 2 *)
Definition p_Upsi1_UDDUUUpsi2 : (U @ psi' 1) [>] (U @ D @ D @ U @ U @ U @ psi' 2) :=
  Step DU (U @@@ D @@@ D @@@ Hole) sub_Upsi1_UDDUUUpsi2 DU_in fact_term_bis_Upsi1 (term_bis_refl (U @ D @ D @ U @ U @ U @ psi' 2)).

(* Two-step reduction psi ->> U D D U U U @ psi' 2 *)
Definition s_psi_UDDUUUpsi2 : psi ->> (U @ D @ D @ U @ U @ U @ psi' 2) := Cons s_psi_Upsi1 p_Upsi1_UDDUUUpsi2.

(* Substitution for step U D D U U U @ psi' 2 -> U D U U @ psi' 2 *)
Definition sub_UDDUUUpsi2_UDUUpsi2 (x : X) : term :=
  match x with
  | 1 => U @ U @ psi' 2
  | _ => Var x
  end.

Lemma fact_term_bis_UDDUUUpsi2 :
  fill (U @@@ D @@@ Hole) (substitute sub_UDDUUUpsi2_UDUUpsi2 (lhs DU))
  [~]
  (U @ D @ D @ U @ U @ U @ psi' 2).
Proof.
(* more of the same *)
Admitted.

(* Step U D D U U U @ psi' 2 -> U D U U @ psi' 2 *)
Definition p_UDDUUUpsi2_UDUUpsi2 : (U @ D @ D @ U @ U @ U @ psi' 2) [>] (U @ D @ U @ U @ psi' 2) :=
  Step DU (U @@@ D @@@ Hole) sub_UDDUUUpsi2_UDUUpsi2 DU_in fact_term_bis_UDDUUUpsi2 (term_bis_refl (U @ D @ U @ U @ psi' 2)).

(* Three-step reduction psi ->> U D U U @ psi' 2 *)
Definition s_psi_UDUUpsi2 : psi ->> (U @ D @ U @ U @ psi' 2) := Cons s_psi_UDDUUUpsi2 p_UDDUUUpsi2_UDUUpsi2.

(* Substitution for step U D U U @ psi' 2 -> U U @ psi' 2 *)
Definition sub_UDUUpsi2_UUpsi2 (x : X) : term :=
  match x with
  | 1 => U @ psi' 2
  | _ => Var x
  end.

Lemma fact_term_bis_UDUUpsi2 :
  fill (U @@@ Hole) (substitute sub_UDUUpsi2_UUpsi2 (lhs DU))
  [~]
  (U @ D @ U @ U @ psi' 2).
Proof.
(* more of the same *)
Admitted.

(* Step U D U U @ psi' 2 -> U U @ psi' 2 *)
Definition p_UDUUpsi2_UUpsi2 : (U @ D @ U @ U @ psi' 2) [>] (U @ U @ psi' 2) :=
  Step DU (U @@@ Hole) sub_UDUUpsi2_UUpsi2 DU_in fact_term_bis_UDUUpsi2 (term_bis_refl (U @ U @ psi' 2)).

(* Four-step reduction psi ->> U U @ psi' 2 *)
Definition s_psi_UUpsi2 : psi ->> (U @ U @ psi' 2) := Cons s_psi_UDUUpsi2 p_UDUUpsi2_UUpsi2.

(*
   All reductions defined so far are really just examples and we now turn
   to parameterized reductions and eventually build up to an infinite
   reduction.

   TODO: complete the above examples, or get rid of the incomplete ones, or
   maybe even add a few.
*)

(* Substitution for step D^Sn @ U^Sn @ t -> D^n @ U^n @ t *)
Definition sub_DSnUSnt_DnUnt n t (x : X) : term :=
  match x with
  | 1 => Unt n t
  | _ => Var x
  end.

Lemma fact_term_bis_DSnUSnt :
  forall (n : nat) (t : term),
    fill (Dnc n Hole) (substitute (sub_DSnUSnt_DnUnt n t) (lhs DU))
    [~]
    DnUnt (S n) t.
Proof.
intros n t.
rewrite fill_DnHole_t.
unfold DnUnt.
simpl.
rewrite DDnt_eq_DnDt.
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

Lemma fact_term_eq_DnUnt :
  forall (n : nat) (t : term),
    fill (Dnc n Hole) (substitute (sub_DSnUSnt_DnUnt n t) (rhs DU))
    =
    DnUnt n t.
Proof.
induction n; intro t; simpl.
reflexivity.
simpl in IHn.
rewrite UUnt_eq_UnUt.
rewrite IHn with (U @ t).
unfold DnUnt; simpl.
rewrite UUnt_eq_UnUt.
reflexivity.
Qed.

Lemma fact_term_bis_DnUnt :
  forall (n : nat) (t : term),
    fill (Dnc n Hole) (substitute (sub_DSnUSnt_DnUnt n t) (rhs DU))
    [~]
    DnUnt n t.
Proof.
intros n t.
rewrite fact_term_eq_DnUnt.
apply term_bis_refl.
Qed.

(* Step D^Sn @ U^Sn @ t -> D^n @ U^n @ t *)
Definition p_DSnUSnt_DnUnt n t : DnUnt (S n) t [>] DnUnt n t :=
  Step DU (Dnc n Hole) (sub_DSnUSnt_DnUnt n t) DU_in (fact_term_bis_DSnUSnt n t) (fact_term_bis_DnUnt n t).

(* n-step reduction D^n @ U^n @ t ->> t *)
Fixpoint s_DnUnt_t n t : DnUnt n t ->> t :=
  match n return DnUnt n t ->> t with
  | O   => Nil' t
  | S n => snoc (p_DSnUSnt_DnUnt n t) (s_DnUnt_t n t)
  end.

(* n-step reduction psi n ->> U @ psi (S n) *)
Program Definition s_psin_UpsiSn n : psi' n ->> (U @ (psi' (S n))) :=
  s_DnUnt_t (S (2 * n)) (U @ psi' (S n)).
Next Obligation.
symmetry.
apply psin_eq_DS2nUS2nUpsiSn.
Defined.

(*
   Now we slightly adjust these sequences to take place under U^m.

   (So the above were still examples.)
*)

Lemma fact_term_bis_UmDSnUSnt :
  forall (m n : nat) (t : term),
    fill (Unc m (Dnc n Hole)) (substitute (sub_DSnUSnt_DnUnt n t) (lhs DU))
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
    fill (Unc m (Dnc n Hole)) (substitute (sub_DSnUSnt_DnUnt n t) (rhs DU))
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
    fill (Unc m (Dnc n Hole)) (substitute (sub_DSnUSnt_DnUnt n t) (rhs DU))
    [~]
    Unt m (DnUnt n t).
Proof.
intros m n t.
rewrite fact_term_eq_UmDnUnt.
apply term_bis_refl.
Qed.

(* Step U^m @ D^Sn @ U^Sn @ t -> U^m @ D^n @ U^n @ t *)
Definition p_UmDSnUSnt_UmDnUnt m n t : Unt m (DnUnt (S n) t) [>] Unt m (DnUnt n t) :=
  Step DU (Unc m (Dnc n Hole)) (sub_DSnUSnt_DnUnt n t) DU_in (fact_term_bis_UmDSnUSnt m n t) (fact_term_bis_UmDnUnt m n t).

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
assert (H :Unt n (DnUnt (S (2 * n)) (U @ psi' (S n))) ->> Unt n (U @ psi' (S n))).
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
Admitted.

(* Omega-step reduction psi ->> UUU... *)
Definition s_psi_repeat_U : psi ->> repeat_U :=
  Lim s_psi_Unpsin converges_Unpsin.

(*
   It should be noted that at this point, nothing has been said yet about
   well-formedness properties of s_psi_repeat_U. More specifically,

   1) s_psi_Unpsin might not have a well-defined limit
   2) this limit might have nothing to do with repeat_U

   We address 1 by proving the 'wf' property and 2 follows by the definition
   of sequences (so 2 is now moot).
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

Lemma s_UmDSnUSnt_Umt_is_cons :
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
induction n as [| n IH]; simpl;
unfold s_Unpsin_USnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl); intro r.
exists (inl _ tt).
apply embed_refl.
revert r.
rewrite (plus_SnO n).
intro r.
destruct (s_UmDSnUSnt_Umt_is_cons (S n) (n + n) (U @ psi' (S (S n)))) as [s [q [p H]]].
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

Lemma weakly_convergent_s_psi_Unpsin :
  forall n : nat, weakly_convergent (s_psi_Unpsin n).
Proof.
intro n.
apply weakly_convergent_finite.
apply finite_s_psi_Unpsin.
Qed.

Lemma pred_s_psi_Unpsin :
  forall n m i,
    n <= m ->
    exists j,
      (s_psi_Unpsin m)[j] = (s_psi_Unpsin n)[i].
Proof.
intros n m i H.
induction H as [| m H IH].
exists i.
reflexivity.
destruct IH as [j IH].
destruct (pred_append (s_psi_Unpsin m) (s_Unpsin_USnpsiSn m) j) as [k H1].
exists k.
rewrite <- IH.
rewrite <- H1.
reflexivity.
Qed.

(* this is just ridiculous *)
Lemma diei : forall d, exists i : pred_type (s_psi_Unpsin (S d)), exists t, JMeq i (inl t tt).
intro d.
simpl.
generalize (s_psi_Unpsin d).
induction d as [| d IH]; simpl;
unfold s_Unpsin_USnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl); intro r.
exists (inl _ tt).
exists (pred_type r).
reflexivity.
revert r.
rewrite (plus_SnO d).
intro r.
destruct (s_UmDSnUSnt_Umt_is_cons (S d) (d + d) (U @ psi' (S (S d)))) as [s [q [p H]]].
rewrite H.
exists (inl _ tt).
simpl.
exists ((fix pred_type (s0 t0 : term) (r0 : s0 ->> t0) {struct r0} :
         Type :=
           match r0 with
           | Nil _ => False
           | Cons s1 t1 r1 _ _ => (unit + pred_type s1 t1 r1)%type
           | Lim s1 ts f _ _ =>
               {n : nat & pred_type s1 (ts n) (f n)}
           end) psi s
          ((fix append_rec (s0 t0 : term) (u : term) (q0 : t0 ->> u) {struct q0} :
              s0 ->> t0 -> s0 ->> u :=
              match
                q0 in (sequence _ t1 u0) return (s0 ->> t1 -> s0 ->> u0)
              with
              | Nil t1 => fun r0 : s0 ->> t1 => r0
              | Cons s1 t1 q1 u0 p0 =>
                  fun r0 : s0 ->> s1 => Cons (append_rec s0 s1 t1 q1 r0) p0
              | Lim s1 ts1 f u0 c =>
                  fun r0 : s0 ->> s1 =>
                  Lim
                    (fun o : nat =>
                       (append_rec s0 s1 (ts1 o) (f o) r0))
                    c
              end) psi
             (U @ Unt d (DnUnt (S (S (S (d + d)))) (U @ psi' (S (S d))))) s
             ((fix snoc_rec (s0 t0 : term) (u : term) (r0 : t0 ->> u) {struct r0} :
                 s0[>]t0 -> s0 ->> u :=
                 match
                   r0 in (sequence _ t1 u0) return (s0[>]t1 -> s0 ->> u0)
                 with
                 | Nil t1 => fun p0 : s0[>]t1 => Cons (Nil' s0) p0
                 | Cons s1 t1 q0 u0 o =>
                     fun p0 : s0[>]s1 => Cons (snoc_rec s0 s1 t1 q0 p0) o
                 | Lim s1 ts f u0 c =>
                     fun p0 : s0[>]s1 =>
                     Lim
                       (fun o : nat =>
                          (snoc_rec s0 s1 (ts o) (f o) p0))
                       c
                 end)
                (U @ Unt d (DnUnt (S (S (S (d + d)))) (U @ psi' (S (S d)))))
                (U @ Unt d (DnUnt (S (S (d + d))) (U @ psi' (S (S d))))) s
                ((fix snoc_rec (s0 t0 : term) (u : term) (r0 : t0 ->> u) {struct r0} :
                    s0[>]t0 -> s0 ->> u :=
                    match
                      r0 in (sequence _ t1 u0) return (s0[>]t1 -> s0 ->> u0)
                    with
                    | Nil t1 => fun p0 : s0[>]t1 => Cons (Nil' s0) p0
                    | Cons s1 t1 q0 u0 o =>
                        fun p0 : s0[>]s1 => Cons (snoc_rec s0 s1 t1 q0 p0) o
                    | Lim s1 us f u0 c =>
                        fun p0 : s0[>]s1 =>
                        Lim
                          (fun o : nat =>
                             (snoc_rec s0 s1 (us o) (f o) p0))
                          c
                    end)
                   (U @ Unt d (DnUnt (S (S (d + d))) (U @ psi' (S (S d)))))
                   (U @ Unt d (DnUnt (S (d + d)) (U @ psi' (S (S d))))) s q
                   (p_UmDSnUSnt_UmDnUnt (S d) (S (d + d))
                      (U @ psi' (S (S d)))))
                (p_UmDSnUSnt_UmDnUnt (S d) (S (S (d + d)))
                   (U @ psi' (S (S d))))) r)).
reflexivity.
Qed.

Require Import Lt.

Lemma embed_s_psi_Unpsin_pred_lt :
  forall d n i,
    embed (s_psi_Unpsin d) ((s_psi_Unpsin n)[seq i]) ->
    d < n.
Proof.
intros d n i H.
destruct (le_or_lt n d) as [N | N].
destruct (pred_s_psi_Unpsin (m := d) i) as [j H1].
assumption.
rewrite <- H1 in H.
contradict H.
apply embed_not_pred_right.
assumption.
Qed.

Lemma kkk :
  forall d n i,
    term_eq_up_to d (Unt n (psi' n)) repeat_U ->
    embed (s_psi_Unpsin n) ((s_psi_Unpsin (S n))[seq i]) ->
    term_eq_up_to d ((s_psi_Unpsin (S n))[1 i]) repeat_U.
Proof.
induction n as [| n IH]; simpl; intros i H1 H2.
clear H2.
unfold s_Unpsin_USnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
Admitted.

Program Definition sdfds :
  forall d n i,
    embed (s_psi_Unpsin d) ((s_psi_Unpsin n)[seq i]) ->
    exists j, ((s_psi_Unpsin n)[seq i])[seq j] = s_psi_Unpsin d := _.
Next Obligation.
destruct (pred_trans (s_psi_Unpsin n) i j) as [k H1].
rewrite <- H1.
(* This cannot be proved from this context *)
admit.
Defined.
Next Obligation.
admit.
Defined.

Lemma all_terms_eq_up_to_d_s_UdDnUnt_Udt_repeat_U :
  forall d n t,
    all_terms_eq_up_to d (s_UmDnUnt_Umt d n t) repeat_U.
Proof.
intros d n t.
induction n as [| n IH]; simpl.
apply term_eq_up_to_n_Unt_repeat_U.
apply all_terms_eq_up_to_snoc.
apply term_eq_up_to_n_Unt_repeat_U.
apply IH.
Qed.

Lemma all_terms_eq_up_to_d_s_Udpsid_USdpsiSd_repeat_U :
  forall d,
    all_terms_eq_up_to d (s_Unpsin_USnpsiSn d) repeat_U.
Proof.
intro d.
unfold s_Unpsin_USnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl).
apply all_terms_eq_up_to_snoc.
apply term_eq_up_to_n_Unt_repeat_U.
apply all_terms_eq_up_to_d_s_UdDnUnt_Udt_repeat_U.
Qed.

(* This reduction is weakly convergent *)
Lemma weakly_convergent_s_psi_repeat_U :
  weakly_convergent s_psi_repeat_U.
Proof.
split.
apply weakly_convergent_s_psi_Unpsin.
intro d.
exists d.
intros [n i] H1.
simpl in * |- *.
assert (H2 := embed_s_psi_Unpsin_pred_lt d n i H1).
assert (H3 := term_eq_up_to_n_Unt_repeat_U d (psi' d)). (* right side of s_psi_Unpsin d *)


induction n as [| n IHn].
inversion H2.
(*Require Import Compare.
destruct (discrete_nat d n N) as [N1 | [m N1]].*)
assert (H4 : exists m, S (d + m) = n).
admit. (* TODO *)
clear H2.
destruct H4 as [m H4].
revert i H1.
rewrite <- H4.
clear H4.
intros i H1.
induction m as [| m IHm].
simpl in * |- *.
assert (J : forall n, n + 0 = n).
admit. (* TODO *)
revert i H1.
rewrite (J d).
clear J.
intros i H1.
induction d as [| d IHd].
constructor.
simpl.




(*
exists d.
intros [n i] H.
simpl in * |- *.
destruct (le_or_lt n d) as [N | N].
destruct (pref_s_psi_Unpsin (m := d) i) as [j H1].
assumption.
rewrite <- H1 in H.
contradict H.
apply embed_not_pref_right.
*)
Admitted.

(* This reduction is weakly convergent *)
(* Version for pref_type lim instead of nat *)
(*
Lemma weakly_convergent_s_psi_repeat_U :
  weakly_convergent s_psi_repeat_U.
Proof.
split.
apply weakly_convergent_s_psi_Unpsin.
intro d.
simpl.
destruct (diei d) as [i [t Ht]].
exists (existT (fun n => pref_type (s_psi_Unpsin n)) (S d) i).
intros [n j] H.
simpl in * |- *.


split.
apply weakly_convergent_s_psi_Unpsin.
intro d.
simpl.
assert (M : finite (s_psi_Unpsin (S d))).
apply finite_s_psi_Unpsin.
generalize_eqs M.
destruct r.
admit. (* TODO: absurd case *)
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.

(* TODO: how can we insert inl_tt here and show it has the right type later??? *)
(* maybe use refine? have a look at a proof term for 'exist' tactic... *)

assert (i : pref_type (s_psi_Unpsin (S d))).
simpl.
rewrite <- x.
exact (inl (pref_type r) tt).


simpl.
unfold s_Unpsin_USnpsiSn; simpl; unfold eq_rect_r; repeat (elim_eq_rect ; simpl).

exists (existT (fun n => pref_type (s_psi_Unpsin n)) (S d) (inl _ tt)).
*)

(* psi rewrites to repeat_D *)
Definition s_psi_repeat_D : psi ->> repeat_D.
(* TODO: same construction as psi ->> repeat_U *)
Admitted.

(* TODO: also include wf properties of the reductions *)
Definition unique_normal_forms :=
  forall t u v,
    t ->> u ->
    t ->> v ->
    normal_form (system := UNWO_trs) u ->
    normal_form (system := UNWO_trs) v ->
    u [~] v.

Lemma no_unique_normal_forms :
  ~ unique_normal_forms.
Proof.
intros H.
apply neq_D_U.
apply (H psi).
exact s_psi_repeat_D.
exact s_psi_repeat_U.
exact nf_D.
exact nf_U.
Qed.

(* TODO: generalize the result, also using weak orthogonality *)

(*
   What follows is an alternative (actually the original) definition of psi
   and a proof that it is equal to the new psi used above.

   Indeed, the remaining is only for 'fun'.
*)

(* D^n U^Sn D^SSn U^SSSn ... *)
CoFixpoint oldpsi' n : term :=
  (cofix Dnt (d : nat) :=
    match d with
    | O   => (cofix USnt (u : nat) :=
               match u with
               | O   => U @ oldpsi' (S (S n))
               | S u => U @ (USnt u)
               end) (S n)
    | S d => D @ (Dnt d)
    end) (S n).

(* DUUDDDUUUU... *)
Definition oldpsi := oldpsi' 0.

Lemma UUSnt_eq_USnUt :
  forall n t,
    (U @ (cofix USnt (u : nat) : term :=
            match u with
            | 0 => t
            | S u0 => U @ USnt u0
            end) n)
    =
    (cofix USnt (u : nat) : term :=
       match u with
       | 0 => U @ t
       | S u0 => U @ USnt u0
       end) n.
Proof.
induction n; intro t.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ USnt u0
      end) 0)).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ USnt u0
       end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ USnt u0
       end) (S n))).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
      match u with
      | 0 => U @ t
      | S u0 => U @ USnt u0
      end) (S n))).
simpl.
rewrite IHn with t.
reflexivity.
Qed.

(* Terrible lemma that should help proving psi n and oldpsi 2n equal *)
Lemma zo :
  forall n t,
    (cofix D2nDt (d : nat) :=
      match d with
      | O   => D @ (cofix U2nt (u : nat) :=
                 match u with
                 | O   => t
                 | S u => U @ U @ (U2nt u)
                 end) (S n)
      | S d => D @ D @ (D2nDt d)
      end) n
    =
    (cofix Dnt (d : nat) :=
      match d with
      | O   => (cofix USnt (u : nat) :=
                 match u with
                 | O   => U @ t
                 | S u => U @ (USnt u)
                 end) (S (n + n))
      | S d => D @ (Dnt d)
      end) (S (2 * n)).
Proof.
induction n; intro t; simpl.
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
      match d with
      | 0 =>
          D @
          (cofix U2nt (u : nat) : term :=
             match u with
             | 0 => t
             | S u0 => U @ U @ U2nt u0
             end) 1
      | S d0 => D @ D @ D2nDt d0
      end) 0)).
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
                match u with
                | 0 => t
                | S u0 => U @ U @ U2nt u0
                end) 1)).
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ t
             | S u0 => U @ USnt u0
             end) 1
      | S d0 => D @ Dnt d0
      end) 1)).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ t
             | S u0 => U @ USnt u0
             end) 1)).
simpl.
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
       match u with
       | 0 => t
       | S u0 => U @ U @ U2nt u0
       end) 0)).
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          U @
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ t
             | S u0 => U @ USnt u0
             end) 0
      | S d0 => D @ Dnt d0
      end) 0)).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
                match u with
                | 0 => U @ t
                | S u0 => U @ USnt u0
                end) 0)).
simpl.
destruct t; reflexivity.
rewrite (peek_eq ((cofix D2nDt (d : nat) : term :=
      match d with
      | 0 =>
          D @
          (cofix U2nt (u : nat) : term :=
             match u with
             | 0 => t
             | S u0 => U @ U @ U2nt u0
             end) (S (S n))
      | S d0 => D @ D @ D2nDt d0
      end) (S n))).
rewrite (peek_eq ((cofix U2nt (u : nat) : term :=
             match u with
             | 0 => t
             | S u0 => U @ U @ U2nt u0
             end) (S (S n)))).
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
      match d with
      | 0 =>
          (cofix USnt (u : nat) : term :=
             match u with
             | 0 => U @ t
             | S u0 => U @ USnt u0
             end) (S (S (n + S n)))
      | S d0 => D @ Dnt d0
      end) (S (S (n + S (n + 0)))))).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
                match u with
                | 0 => U @ t
                | S u0 => U @ USnt u0
                end) (S (S (n + S n))))).
simpl.
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
       match d with
       | 0 =>
           U @
           (cofix USnt (u : nat) : term :=
              match u with
              | 0 => U @ t
              | S u0 => U @ USnt u0
              end) (S (n + S n))
       | S d0 => D @ Dnt d0
       end) (S (n + S (n + 0))))).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
                 match u with
                 | 0 => U @ t
                 | S u0 => U @ USnt u0
                 end) (S (n + S n)))).
simpl.
rewrite UU2nt_eq_U2nUt_unfolded with (S n) t.
rewrite UU2nt_eq_U2nUt_unfolded with (S n) (U @ t).
rewrite IHn with (U @ U @ t).
rewrite UUSnt_eq_USnUt with (n + S n) (U @ t).
rewrite UUSnt_eq_USnUt with (n + S n) (U @ U @ t).
simpl.
rewrite (eq_sym (plus_n_Sm n n)).
rewrite (eq_sym (plus_n_Sm n (n + 0))).
reflexivity.
Qed.

Lemma psin_eq_oldpsi2n :
  forall n,
    psi' n [~] oldpsi' (2 * n).
Proof.
(* TODO: should be somehow possible to show, using lemma zo *)
Admitted.

(* This increases confidence in correctness of psi :) *)
Lemma psi_eq_oldpsi :
  psi [~] oldpsi.
Proof.
apply psin_eq_oldpsi2n.
Qed.
