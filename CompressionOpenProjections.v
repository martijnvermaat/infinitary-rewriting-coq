Require Export RewritingOpenProjections.


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
Definition sequence_succ_intro s s_term s_step
  (H : source s_step [=] terms s (length s) /\ target s_step [=] s_term)
  :=
  Sequence (succ (length s))
    (fun alpha => if (alpha <= (length s)) then (terms s alpha) else s_term)
    (fun alpha => if (alpha < (length s)) then (steps s alpha) else s_step)
    (fun alpha H' => if (alpha < (length s)) then (locally_continuous s alpha H') else H).
*)

Definition sequence_succ_elim s_length s_terms (s_steps : ord -> step) s_lc :=
  Sequence s_length s_terms s_steps (fun alpha H => s_lc alpha (ord'_lt_succ_right H)).

Lemma distance_decreasing_succ_elim :
  forall s_length s_terms s_steps s_lc lambda,
    distance_decreasing (Sequence (succ s_length) s_terms s_steps s_lc) lambda ->
    distance_decreasing (sequence_succ_elim s_length s_terms s_steps s_lc) lambda.
Proof.
intros.
intro n.
destruct (H n) as [alpha' H'].
exists alpha'.
apply H'.
Qed.

Lemma depth_increasing_succ_elim :
  forall s_length s_terms s_steps s_lc lambda,
    depth_increasing (Sequence (succ s_length) s_terms s_steps s_lc) lambda ->
    depth_increasing (sequence_succ_elim s_length s_terms s_steps s_lc) lambda.
Proof.
intros.
intro n.
destruct (H n) as [alpha' H'].
exists alpha'.
apply H'.
Qed.

Lemma weakly_convergent_succ_elim :
  forall s_length s_terms s_steps s_lc,
    weakly_convergent (Sequence (succ s_length) s_terms s_steps s_lc) ->
    weakly_convergent (sequence_succ_elim s_length s_terms s_steps s_lc).
Proof.
intros.
intros lambda Hlim Hlambda.
apply distance_decreasing_succ_elim.
apply H.
assumption.
exact (ord'_le_succ_right Hlambda).
Qed.

Lemma strongly_convergent_succ_elim :
  forall s_length s_terms s_steps s_lc,
    strongly_convergent (Sequence (succ s_length) s_terms s_steps s_lc) ->
    strongly_convergent (sequence_succ_elim s_length s_terms s_steps s_lc).
Proof.
intros.
split.
apply weakly_convergent_succ_elim.
apply H.
intros.
apply depth_increasing_succ_elim.
apply H.
assumption.
exact (ord'_le_succ_right H1).
Qed.

Lemma le_omega_elim :
  forall alpha P,
    alpha <= omega ->
    (alpha < omega -> P) ->
    (alpha = omega -> P) ->
    P.
Proof.
intros alpha P H H1 H2.
destruct alpha as [alpha g].
destruct alpha.
apply H1.
(*
unfold ord_lt.
simpl.
unfold ord'_lt.
simpl.
exists (existT (fun n => pred_type n) 2 (inl (pred_type 1) tt)).
*)
Admitted.

Lemma compression :
  trs_left_linear system ->
  forall s : sequence system,
    strongly_convergent s ->
    exists s' : sequence system,
      strongly_convergent s' /\
      length s' <= omega /\
      terms s zero [=] terms s' zero /\
      terms s (length s) [=] terms s' (length s').
Proof.
intros LL s SC.
destruct s as [s_length s_terms s_steps s_lc].
destruct s_length as [s_length s_length_good].
induction s_length as [| s_length IH | f IH].

(* length s = Zero *)
exists (Sequence (exist good Zero s_length_good) s_terms s_steps s_lc).
split.
assumption.
split.
apply Ord'_le_Zero.
split; simpl; apply term_eq_refl.

(* length s = Succ _ *)
(* Apply IH for first s_length segment *)
assert (t := IH s_length_good (fun alpha H => s_lc alpha (ord'_lt_succ_right H))
             (strongly_convergent_succ_elim (exist good s_length s_length_good) s_terms s_steps s_lc SC)).
elim t.
intros.
(* gevalsonderscheid voor length x <= omega: < omega of = omega *)
apply (le_omega_elim (length x)).
apply H.
intro.
admit.
admit.

(* length s = Limit _ *)
admit.

Qed.

Local Close Scope ord_scope.

End Compression.
