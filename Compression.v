Require Export Rewriting.


Section Compression.

Variable F : signature.
Variable X : variables.

Notation term := (term F X).
Notation rule := (rule F X).
Notation trs := (trs F X).

Variable system : trs.

Notation step := (step system).

Local Open Scope ord_scope.


(*
Definition terms_succ_intro :
  forall (t : term) (kappa : ord) (s_terms : forall alpha, alpha <= kappa -> term),
  forall alpha, alpha <= succ kappa -> term :=
  fun t kappa s_terms alpha H =>
  match H return term with
  Ord'_le_Zero beta => t
  | _ => t
  end.
*)


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
(*destruct (length x).*)
(* gevalsonderscheid voor length x <= omega: < omega of = omega *)
admit.

(* length s = Limit _ *)
admit.

Qed.

Local Close Scope ord_scope.

End Compression.
