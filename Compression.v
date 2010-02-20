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
    (LC : (forall (alpha : ord) (H : alpha < succ s_length),
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
exact (LC alpha (ord'_lt_succ_right H)).
Qed.

Lemma strongly_convergent_succ_elim :
  forall
    (s_length : ord)
    (s_terms : (forall alpha : ord, alpha <= succ s_length -> term))
    (s_terms_pi : (forall alpha H H', s_terms alpha H = s_terms alpha H'))
    (s_steps : (forall alpha : ord, alpha < succ s_length -> step))
    (s_steps_pi : (forall alpha H H', s_steps alpha H = s_steps alpha H'))
    (LC : (forall alpha (H : alpha < succ s_length),
      source (s_steps alpha H) [=] s_terms alpha (ord'_lt_ord'_le H) /\
      target (s_steps alpha H) [=] s_terms (succ alpha) (ord'_lt_ord'_le_succ H)))
    (SC : strongly_convergent (Sequence (succ s_length) s_terms s_terms_pi s_steps s_steps_pi LC)),
    strongly_convergent (Sequence
      s_length
      (fun alpha H => (s_terms alpha (ord'_le_succ_right H)))
      (fun alpha H H' => s_terms_pi alpha (ord'_le_succ_right H) (ord'_le_succ_right H'))
      (fun alpha H => (s_steps alpha (ord'_lt_succ_right H)))
      (fun alpha H H' => s_steps_pi alpha (ord'_lt_succ_right H) (ord'_lt_succ_right H'))
      (locally_convergent_succ_elim s_length s_terms s_terms_pi s_steps s_steps_pi LC)).
Proof.
intros.
unfold strongly_convergent.
split.
unfold weakly_convergent.
Admitted.

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
destruct s as [s_length s_terms s_terms_pi s_steps s_steps_pi LC].
destruct s_length as [s_length s_length_good].
induction s_length as [| s_length IH | f IH].

(* length s = Zero *)
exists (Sequence (exist good Zero s_length_good) s_terms s_terms_pi s_steps s_steps_pi LC).
split.
assumption.
split.
apply Ord'_le_Zero.
split; simpl; apply term_eq_refl.

(* length s = Succ _ *)
(* Apply IH for first s_length segment *)

assert (IH' := IH
  s_length_good
  (fun alpha H => (s_terms alpha (ord'_le_succ_right H)))
  (fun alpha H H' => s_terms_pi alpha (ord'_le_succ_right H) (ord'_le_succ_right H'))
  (fun alpha H => (s_steps alpha (ord'_lt_succ_right H)))
  (fun alpha H H' => s_steps_pi alpha (ord'_lt_succ_right H) (ord'_lt_succ_right H'))
  (locally_convergent_succ_elim (exist good s_length s_length_good) s_terms s_terms_pi s_steps s_steps_pi LC)
  (strongly_convergent_succ_elim (exist good s_length s_length_good) s_terms s_terms_pi s_steps s_steps_pi LC SC)).
elim IH'.
intros.
(* gevalsonderscheid voor length x <= omega: < omega of = omega *)
admit.

(* length s = Limit _ *)
admit.

Qed.

Local Close Scope ord_scope.

End Compression.
