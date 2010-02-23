Require Export Rewriting.


Section Compression.

Variable F : Signature.
Variable X : Variables.

Notation term := (term F X).
Notation rule := (rule F X).

Variable system : trs F X.

Notation step := (step system).

(* From now on, the default scope is that of our ordinals *)
Local Open Scope ord_scope.
(*
Inductive ord'_le : ord' -> ord' -> Prop :=
  | Ord'_le_Zero  : forall alpha,
                      Zero <=' alpha
  | Ord'_le_Succ  : forall alpha beta i,
                      alpha <=' pred beta i ->
                      Succ alpha <=' beta
  | Ord'_le_Limit : forall f beta,
                      (forall n, f n <=' beta) ->
                      Limit f <=' beta
where "alpha <=' beta" := (ord'_le alpha beta) : ord'_scope.

Definition ord_le (alpha beta : ord) : Prop :=
  proj1_sig alpha <=' proj1_sig beta.
Infix " <= " := ord_le : ord_scope.

*)

Local Open Scope ord'_scope.


Lemma le_ord_elim :
  forall alpha beta,
    alpha <=' beta ->
    forall P : Prop,
    (alpha <' beta -> P) ->
    (alpha = beta -> P) ->
    P.
induction 1; intros P Hlt Heq.
destruct alpha.
apply Heq.
reflexivity.
apply Hlt.
unfold ord'_lt.
exists (inl (pred_type alpha) tt).
constructor.
apply Hlt.


Ltac expl_case x :=
  generalize (refl_equal x); pattern x at -1; case x; intros until 1.

Lemma uu :
  forall alpha, 
  good alpha -> 
  (exists i : pred_type alpha, True) \/ Zero = alpha.
Proof.
induction alpha as [alpha | alpha IH | f IH]; simpl; intro g.
right; reflexivity.
left.
exists (inl _ tt); constructor.
left.
elim (IH 1 (proj1 (g 1))); intro H.
destruct H as [i H'].
exists (existT (fun n => pred_type (f n)) 1 i).
constructor.
destruct (g 0) as [H1 H2].
assert (H3 : f 0 <' f 1).
apply H2; auto.
unfold ord'_lt in H3.
elim H3; intros i _.
rewrite <- H in i.
elim i.
Qed.


Lemma xx :
  forall alpha beta,
  alpha <=' beta ->
  good alpha ->
  good beta ->
  (exists i, alpha <=' pred beta i) \/ alpha = beta.
Proof.
induction 1.
intros ga gb.

elim (uu alpha gb); intro H.
destruct H as [i _].
left; exists i; constructor.
right; exact H.
intros ga gb.

elim IHord'_le.
intro.
elim H0; intros j H1.
left.
exists i.
apply (Ord'_le_Succ _ j).
exact H1.
intro H0.
clear IHord'_le H.
rewrite H0; clear H0.
induction beta.
elim i.
destruct i as [[]|i']; simpl in *|-*.
right.
reflexivity.
left.
elim (IHbeta i').
intro H1.
elim H1; intros j H1'.
exists (inr unit j).
exact H1'.
intro H1.
exists (inl _ tt).
rewrite H1.
apply ord'_le_refl.
exact gb.
left.
simpl in i.
elim i; intros n i'.


elim (H n i').
intro Hl.
elim Hl; intros j Hl'.
simpl.
exists (existT (fun n => pred_type (o n)) n j).
exact Hl'.
intro Hr.
simpl.
rewrite Hr.
clear Hr i' H i.
simpl in gb.
destruct (proj2 (gb n) (S n)) as [i H].
auto.
exists (existT (fun n => (pred_type (o n))) (S n) i).
exact H.


simpl in gb.
apply (gb n).
exact ga.

Focus 2.
simpl.
intros ga gb.
left.

(* ?? *)

destruct beta.

Focus 2.

exists (inl _ tt).
constructor.
simpl.
intro n.


elim (H0 n).
intro H1.




destruct (H0 0 ga) as [[i H1]|H1].
exists i.
constructor.

intro n.



Lemma yy :
  forall alpha beta,
  alpha <=' Succ beta ->
  alpha <=' beta \/ alpha = Succ beta.
Proof.

(*
intros.
inversion_clear H.
left.
constructor.
destruct i as [[]|i']; simpl in *|-*.
*)


Definition terms_succ_intro :
  forall (t : term) (kappa : ord) (s_terms : forall alpha, alpha <= kappa -> term),
  forall alpha, alpha <= succ kappa -> term :=
  fun t kappa s_terms alpha H =>
  match H return term with 
  Ord'_le_Zero beta => t
  | _ => t
  end.
  


(*
Lemma terms_pi_succ_elim :
  forall
    (s_length : ord)
    (s_terms : (forall alpha : ord, alpha <= succ s_length -> term))
    (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H')),
    (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H')),
*)

Lemma locally_convergent_succ_elim :
  forall
    (s_length : ord)
    (s_terms : (forall alpha : ord, alpha <= succ s_length -> term))
    (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H'))
    (s_steps : (forall alpha : ord, alpha < succ s_length -> step))
    (s_steps_pi : (forall alpha H H', s_steps alpha H = s_steps alpha H'))
    (s_lc : (forall (alpha : ord) (H : alpha < succ s_length),
      source (s_steps alpha H) [=]
        s_terms alpha (ord'_lt_ord'_le H) /\
      target (s_steps alpha H) [=]
        s_terms (succ alpha) (ord'_lt_ord'_le_succ H))),
    (forall (alpha : ord) (H : alpha < s_length),
      source (s_steps alpha (ord'_lt_succ_right H)) [=]
        s_terms alpha (ord'_le_succ_right (ord'_lt_ord'_le H)) /\
      target (s_steps alpha (ord'_lt_succ_right H)) [=]
        s_terms (succ alpha)(ord'_le_succ_right (ord'_lt_ord'_le_succ H))).
Proof.
intros.
rewrite
  (s_terms_pi alpha
    (ord'_le_succ_right (ord'_lt_ord'_le H))
    (ord'_lt_ord'_le (ord'_lt_succ_right H))).
rewrite
  (s_terms_pi (succ alpha)
    (ord'_le_succ_right (ord'_lt_ord'_le_succ H))
    (ord'_lt_ord'_le_succ (ord'_lt_succ_right H))).
exact (s_lc alpha (ord'_lt_succ_right H)).
Qed.

Definition sequence_succ_elim
  (s_length : ord)
  (s_terms : (forall alpha : ord, alpha <= succ s_length -> term))
  (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H'))
  (s_steps : (forall alpha : ord, alpha < succ s_length -> step))
  (s_steps_pi : (forall alpha H H', s_steps alpha H = s_steps alpha H'))
  (s_lc : (forall (alpha : ord) (H : alpha < succ s_length),
    source (s_steps alpha H) [=]
      s_terms alpha (ord'_lt_ord'_le H) /\
    target (s_steps alpha H) [=]
      s_terms (succ alpha) (ord'_lt_ord'_le_succ H))) :=
  Sequence
    s_length
    (fun alpha H => (s_terms alpha (ord'_le_succ_right H)))
    (fun alpha H H' => s_terms_pi alpha (ord'_le_succ_right H) (ord'_le_succ_right H'))
    (fun alpha H => (s_steps alpha (ord'_lt_succ_right H)))
    (fun alpha H H' => s_steps_pi alpha (ord'_lt_succ_right H) (ord'_lt_succ_right H'))
    (locally_convergent_succ_elim s_length s_terms s_terms_pi s_steps s_steps_pi s_lc).

Lemma distance_decreasing_succ_elim :
  forall
    (s_length : ord)
    (s_terms : (forall alpha : ord, alpha <= succ s_length -> term))
    (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H'))
    (s_steps : (forall alpha : ord, alpha < succ s_length -> step))
    (s_steps_pi : (forall alpha H H', s_steps alpha H = s_steps alpha H'))
    (s_lc : (forall alpha (H : alpha < succ s_length),
      source (s_steps alpha H) [=] s_terms alpha (ord'_lt_ord'_le H) /\
      target (s_steps alpha H) [=] s_terms (succ alpha) (ord'_lt_ord'_le_succ H)))
    (lambda : ord)
    (Hl : lambda <= s_length)
    (DD : distance_decreasing (Sequence (succ s_length) s_terms s_terms_pi s_steps s_steps_pi s_lc) lambda (ord'_le_succ_right Hl)),
    distance_decreasing (sequence_succ_elim s_length s_terms s_terms_pi s_steps s_steps_pi s_lc) lambda Hl.
Proof.
intros.
intro n.
destruct (DD n).
exists x.
split; simpl.
apply H.
intros beta Hb.
rewrite (s_terms_pi beta (ord'_le_succ_right (ord'_le_trans (ord'_lt_ord'_le Hb) Hl)) (ord'_le_trans (ord'_lt_ord'_le Hb) (ord'_le_succ_right Hl))).
apply H.
Qed.

Lemma depth_increasing_succ_elim :
  forall
    (s_length : ord)
    (s_terms : (forall alpha : ord, alpha <= succ s_length -> term))
    (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H'))
    (s_steps : (forall alpha : ord, alpha < succ s_length -> step))
    (s_steps_pi : (forall alpha H H', s_steps alpha H = s_steps alpha H'))
    (s_lc : (forall alpha (H : alpha < succ s_length),
      source (s_steps alpha H) [=] s_terms alpha (ord'_lt_ord'_le H) /\
      target (s_steps alpha H) [=] s_terms (succ alpha) (ord'_lt_ord'_le_succ H)))
    (lambda : ord)
    (Hl : lambda <= s_length)
    (DD : depth_increasing (Sequence (succ s_length) s_terms s_terms_pi s_steps s_steps_pi s_lc) lambda (ord'_le_succ_right Hl)),
    depth_increasing (sequence_succ_elim s_length s_terms s_terms_pi s_steps s_steps_pi s_lc) lambda Hl.
Proof.
intros.
intro n.
destruct (DD n).
exists x.
split; simpl.
apply H.
intros beta Hb.
rewrite (s_steps_pi beta (ord'_lt_succ_right (ord'_lt_trans_ord'_le_right Hb Hl)) (ord'_lt_trans_ord'_le_right Hb (ord'_le_succ_right Hl))).
apply H.
Qed.

Lemma weakly_convergent_succ_elim :
  forall
    (s_length : ord)
    (s_terms : (forall alpha : ord, alpha <= succ s_length -> term))
    (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H'))
    (s_steps : (forall alpha : ord, alpha < succ s_length -> step))
    (s_steps_pi : (forall alpha H H', s_steps alpha H = s_steps alpha H'))
    (s_lc : (forall alpha (H : alpha < succ s_length),
      source (s_steps alpha H) [=] s_terms alpha (ord'_lt_ord'_le H) /\
      target (s_steps alpha H) [=] s_terms (succ alpha) (ord'_lt_ord'_le_succ H)))
    (WC : weakly_convergent (Sequence (succ s_length) s_terms s_terms_pi s_steps s_steps_pi s_lc)),
    weakly_convergent (sequence_succ_elim s_length s_terms s_terms_pi s_steps s_steps_pi s_lc).
Proof.
intros.
intros lambda Hl Hlim.
apply distance_decreasing_succ_elim.
apply WC.
assumption.
Qed.

Lemma strongly_convergent_succ_elim :
  forall
    (s_length : ord)
    (s_terms : (forall alpha : ord, alpha <= succ s_length -> term))
    (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H'))
    (s_steps : (forall alpha : ord, alpha < succ s_length -> step))
    (s_steps_pi : (forall alpha H H', s_steps alpha H = s_steps alpha H'))
    (s_lc : (forall alpha (H : alpha < succ s_length),
      source (s_steps alpha H) [=] s_terms alpha (ord'_lt_ord'_le H) /\
      target (s_steps alpha H) [=] s_terms (succ alpha) (ord'_lt_ord'_le_succ H)))
    (SC : strongly_convergent (Sequence (succ s_length) s_terms s_terms_pi s_steps s_steps_pi s_lc)),
    strongly_convergent (sequence_succ_elim s_length s_terms s_terms_pi s_steps s_steps_pi s_lc).
Proof.
intros.
unfold strongly_convergent.
split.
apply weakly_convergent_succ_elim.
apply SC.
intros.
apply depth_increasing_succ_elim.
apply SC.
assumption.
Qed.

Lemma compression :
  trs_left_linear system ->
  forall s : sequence system,
    strongly_convergent s ->
    exists s' : sequence system,
      strongly_convergent s' /\
      length s' <= omega /\
      terms s zero (ord_le_zero (length s))
        [=] terms s' zero (ord_le_zero (length s')) /\
      terms s (length s) (ord_le_refl (length s))
        [=] terms s' (length s') (ord_le_refl (length s')).
Proof.
intros LL s SC.
destruct s as [s_length s_terms s_terms_pi s_steps s_steps_pi s_lc].
destruct s_length as [s_length s_length_good].
induction s_length as [| s_length IH | f IH].

(* length s = Zero *)
exists (Sequence (exist good Zero s_length_good) s_terms s_terms_pi s_steps s_steps_pi s_lc).
split.
assumption.
split.
apply Ord'_le_Zero.
split; simpl; apply term_eq_refl.

(* length s = Succ _ *)
(* Apply IH for first s_length segment *)
assert (s := sequence_succ_elim
  (exist good s_length s_length_good) s_terms s_terms_pi s_steps s_steps_pi s_lc).
assert (IH' := IH
  s_length_good
  (fun alpha H => (s_terms alpha (ord'_le_succ_right H)))
  (fun alpha H H' => s_terms_pi alpha (ord'_le_succ_right H) (ord'_le_succ_right H'))
  (fun alpha H => (s_steps alpha (ord'_lt_succ_right H)))
  (fun alpha H H' => s_steps_pi alpha (ord'_lt_succ_right H) (ord'_lt_succ_right H'))
  (locally_convergent_succ_elim (exist good s_length s_length_good) s_terms s_terms_pi s_steps s_steps_pi s_lc)
  (strongly_convergent_succ_elim (exist good s_length s_length_good) s_terms s_terms_pi s_steps s_steps_pi s_lc SC)).
elim IH'.
intros.
destruct (length x).
(* gevalsonderscheid voor length x <= omega: < omega of = omega *)
admit.

(* length s = Limit _ *)
admit.

Qed.

Local Close Scope ord_scope.

End Compression.
