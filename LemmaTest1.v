Require Export Ordinal.

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

Open Scope ord'_scope.
Open Scope ord_scope.

(*
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
*)

Ltac expl_case x :=
  generalize (refl_equal x); pattern x at -1; case x; intros until 1.

(* This is part of ord_le_zero_good and should be separated from it (Ordinals.v) *)
Lemma ord'_le_zero_good :
  forall alpha,
    good alpha ->
    alpha <=' Zero ->
    alpha = Zero.
Proof.
induction alpha as [| | f IH]; intros G H.
reflexivity.
elim (ord'_le_not_succ_zero H).
elimtype False.
apply ord'_lt_zero_zero.
simpl in G.
destruct (G 1) as [G1 Gnm].
destruct (G 2) as [G2 _].
inversion_clear H.
pattern Zero at 1.
rewrite <- (IH 1).
rewrite <- (IH 2).
apply Gnm.
constructor.
assumption.
apply H0.
assumption.
apply H0.
Qed.

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

Lemma vv :
  forall alpha i,
    good alpha -> good (pred alpha i).
Proof.
induction alpha as [| alpha IH | f IH]; intros i g; destruct i.
destruct u.
assumption.
apply IH.
assumption.
apply IH.
apply g.
Qed.

(*
Lemma ww :
  forall f alpha,
    (forall n, exists i, f n <=' pred alpha i) ->
    exists i, Limit f <=' pred alpha i.
Proof.
intros f alpha H.
destruct alpha.
destruct (H 0) as [[] _].
exists (inl _ tt).
constructor.
intro.
destruct (H n) as [[[] | i] H1].
assumption.
apply ord'_le_pred_right with i.
assumption.
*)

Lemma xx :
  forall alpha beta,
  alpha <=' beta ->
  good alpha ->
  good beta ->
  (exists i, alpha <=' pred beta i) \/ alpha = beta.
Proof.
induction 1 as [alpha | alpha beta i H IH | f beta H IH]; intros ga gb.

(* 1. Case Zero <=' pred beta i \/ Zero = beta *)
elim (uu alpha gb); intro H.
destruct H as [i _].
left; exists i; constructor.
right; exact H.

(* 2. Case Succ alpha <=' pred beta i \/ Succ alpha = beta *)
destruct IH as [IH | e].
assumption.
apply vv.
assumption.

(* 2.1 Left side of IH *)
left.
destruct IH as [j IH].
exists i.
apply Ord'_le_Succ with j.
assumption.

(* 2.2 Right side of IH *)
induction beta as [| beta IH | f IH].

(* 2.2.1 Case beta => Zero *)
elim i.

(* 2.2.2 Case beta => Succ beta *)
destruct i as [[] | i].
right.
rewrite e.
reflexivity.
left.
destruct (IH i H e gb) as [[j H1] | H1]; clear IH.
exists (inr unit j).
assumption.
exists (inl _ tt).
rewrite H1.
apply ord'_le_refl.

(* 2.2.3 Case beta => Limit f *)
left.
destruct i as [n i].
destruct (IH n i) as [[j H1] | H1].
assumption.
assumption.
apply gb.
exists (existT (fun n => pred_type (f n)) n j).
assumption.
rewrite H1.
clear H H1 IH e i.
destruct (proj2 (gb n) (S n)) as [i H].
auto.
exists (existT (fun n => (pred_type (f n))) (S n) i).
assumption.

(* 3. Case Limit f <=' pred beta i \/ Limit f = beta *)

(*left.*)
(*induction beta.*)
destruct beta.

(* 3.1 Case beta => Zero *)
destruct (proj2 (ga 0) 1) as [i _].
auto.
rewrite (ord'_le_zero_good (f 1) (proj1 (ga 1)) (H 1)) in i.
elim i.

(* 3.2 Case beta => Succ beta *)
left.
exists (inl _ tt).
constructor.
intro n.
destruct (proj2 (ga n) (S n)) as [i H1].
auto.
simpl.
assert (H2 : f n <' Succ beta).
apply ord'_lt_trans_ord'_le_right with (f (S n)).
exists i.
assumption.
apply H.
unfold ord'_lt in H2.
destruct H2 as [[[] | j] H2].
assumption.
apply ord'_le_pred_right with j.
assumption.

(* 3.3 Case beta => Limit o *)

(* Now we are stuck *)
Admitted.

(*
  The problem with this lemma seems to be the definitions of pred or <=.

  I think we could prove it, if either:

  1) pred_type (Limit f) = nat
     pred (Limit f) n = f n

     instead of

     pred_type (Limit f) = { n : nat & pred_type (f n)
     pred (Limit f) i = match i with
                        | existT n t => pred (f n) t
                        end

     So, predecessors of a limit ordinal would be just the range of its limit
     function instead of predecessors of them.

  2) (forall i, pred (Limit f) i <=' beta) -> Limit f <=' beta

     instead of

     (forall n, f n <=' beta) -> Limit f <=' beta

  Currently, pred and <= just don't seem to fit into each other, and this
  makes IH in this lemma useless.

  Peter Hancock [1] explicitly uses our current definitions for pred and <=,
  but for example in [2], all (f n) are predecessors of (Limit f) like in the
  suggestion above. <= is then taken as the transitive closure of pred.

  Why should the predecessor relation 'always cross a successor', as Hancock
  puts it?

  [1] http://events.cs.bham.ac.uk/mgs2008/notes/proofTheory.pdf
  [2] http://isabelle.in.tum.de/library/HOL/Induct/Tree.html
*)


Close Scope ord_scope.
Close Scope ord'_scope.
