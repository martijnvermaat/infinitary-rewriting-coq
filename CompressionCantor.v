Add LoadPath "./Cantor/prelude".
Add LoadPath "./Cantor/misc".
Add LoadPath "./Cantor/rpo".
Add LoadPath "./Cantor/epsilon0".
Add LoadPath "./Cantor/gamma0".


Require Export RewritingCantor.


Section Compression.

Variable S : signature.
Variable X : variables.

Notation term := (term S X).
Notation rule := (rule S X).
Notation trs := (trs S X).

Variable system : trs.

Notation step := (step system).

Notation source := (@source S X system).
Notation length := (@length S X system).
Notation nf_length := (@nf_length S X system).
Notation terms := (@terms S X system).
Notation steps := (@steps S X system).
Notation Sequence := (@Sequence S X system).

Lemma aaa :
  forall alpha beta,
    alpha <= succ beta -> alpha <= beta.
Proof.
Admitted.

Lemma bbb :
  forall alpha,
    alpha <= alpha.
Proof.
Admitted.

Lemma ccc :
  forall alpha beta,
    alpha < succ beta -> alpha < beta.
Proof.
Admitted.

Program Definition sequence_succ_intro s s_term s_step
  (H : source s_step [=] terms s (length s) (nf_length s) (bbb (length s)) /\ target s_step [=] s_term)
  :=
  Sequence
    (succ (length s))
    (succ_nf (nf_length s))
    (fun alpha nf_alpha H' => match compare alpha (succ (length s)) with
                              | Lt => terms s alpha nf_alpha (aaa alpha (length s) H')
                              | _  => s_term
                              end)
    (fun alpha nf_alpha H' => match compare alpha (length s) with
                              | Lt => steps s alpha nf_alpha (ccc alpha (length s) H')
                              | _  => s_step
                              end)
    _.
Next Obligation.
(* use H and H1 *)
case (trichotomy_inf alpha (length s)).
destruct 1.
assert (M := @local_continuity S X system s).
admit. (*apply (M alpha nf_alpha l).*)
admit. (*rewrite e. apply H and H1 *)
intro.
admit. (* contradict H0 and l *)
Defined.

(*
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
(*destruct (length x).*)
(* gevalsonderscheid voor length x <= omega: < omega of = omega *)
admit.

(* length s = Limit _ *)
admit.

Qed.

*)

End Compression.
