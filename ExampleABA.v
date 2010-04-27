Require Import RewritingOrdinalSequence.

Set Implicit Arguments.

(*
  We construct the TRS with one rule

    ABA : A -> B(A)

  and a convergent reduction of length Omega

    A ->> B(B(B(..)))
*)

(* Signature *)

Inductive symbol : Set := A | B.

Definition beq_symb (f g : symbol) : bool :=
  match f, g with
  | A, A => true
  | B, B => true
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
  | A => 0
  | B => 1
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

(* Function application with no arguments *)
Notation "f !" := (@Fun F X f (vnil fterm)) (at level 70).
Notation "f !!" := (@FFun F X f (vnil fterm)) (at level 70).

(* Function application with one argument *)
Notation "f @ a" := (@Fun F X f (vcons a (vnil term))) (right associativity, at level 75).
Notation "f @@ a" := (@FFun F X f (vcons a (vnil fterm))) (right associativity, at level 75).

(* Some terms *)
Definition test_A : term := A!.
Definition test_BA : term := B @ A!.
Definition test_BBA : term := B @ B @ A!.

(* Finite versions *)
Definition ftest_A : fterm := A!!.
Definition ftest_BA : fterm := B @@ A!!.
Definition ftest_BBA : fterm := B @@ B @@ A!!.

(* B(B(B(...))) *)
CoFixpoint repeat_B : term :=
  B @ repeat_B.

(* Contexts *)

Notation context := (context F X).

(* Function application with one argument *)
Notation "f @@@ a" := (@CFun F X f 0 0 (@refl_equal nat (arity B)) (vnil term) a (vnil term)) (right associativity, at level 75).

Notation id_sub := (empty_substitution F X).

(* Rewriting *)

Notation trs := (trs F X).

(* A -> B(A) *)

Definition ABA_l : fterm := A!!.
Definition ABA_r : fterm := B @@ A!!.

Lemma ABA_wf :
  is_var ABA_l = false /\
  incl (vars ABA_r) (vars ABA_l).
Proof.
split; simpl.
reflexivity.
intros a H.
assumption.
Qed.

Definition ABA : rule := Rule ABA_l ABA_r ABA_wf.
Definition ABA_trs : trs := ABA :: nil.

Lemma ABA_left_linear :
  trs_left_linear ABA_trs.
Proof.
split; constructor.
Qed.

(* Reductions *)
Notation Step := (Step ABA_trs).
Notation Nil := (Nil ABA_trs).

Notation "s [>] t" := (step ABA_trs s t) (at level 40).
Notation "s ->> t" := (sequence ABA_trs s t) (at level 40).

Lemma ABA_in :
  In ABA ABA_trs.
Proof.
left. reflexivity.
Qed.

(* Zero-step reduction A ->> A *)
Definition s_A : (A!) ->> (A!) := Nil (A!).

Lemma fact_term_eq_A :
  @Fun F X A (vmap (substitute id_sub) (vnil fterm)) [=] (A !).
Proof.
intro n.
destruct n; constructor.
intro.
contradiction (vnil False).
Qed.

Require Import Equality.

Lemma fact_term_eq_BA :
  @Fun F X B (vmap (substitute id_sub) (vcons (A !!) (vnil fterm))) [=] (B @ A !).
Proof.
intro n.
destruct n; constructor.
intro i.
dependent destruction i.
apply fact_term_eq_A.
contradiction (vnil False).
Qed.

(* Step A -> B(A) *)
Definition p_A_BA : (A!) [>] (B @ A!) := Step ABA Hole id_sub ABA_in fact_term_eq_A fact_term_eq_BA.

(* Single-step reduction A ->> B(A) *)
Definition s_A_BA : (A!) ->> (B @ A!) := Cons s_A p_A_BA.

Lemma fact_term_eq_BA' :
  (B @ @Fun F X A (vmap (substitute id_sub) (vnil fterm))) [=]
  (B @ @Fun F X A (fun x : Fin 0 => vnil fterm x)).
Proof.
intro n.
destruct n; constructor.
intro i.
dependent destruction i.
apply fact_term_eq_A.
contradiction (vnil False).
Qed.

Lemma fact_term_eq_BBA :
  (B @ @Fun F X B (vmap (substitute id_sub) (vcons (A !!) (vnil fterm)))) [=]
  (B @ B @ @Fun F X A (fun x : Fin 0 => vnil fterm x)).
Proof.
intro n.
destruct n; constructor.
intro i.
dependent destruction i.
apply fact_term_eq_BA.
contradiction (vnil False).
Qed.

(* Step B(A) -> B(B(A)) *)
Definition p_BA_BBA : (B @ A!) [>] (B @ B @ A!) := Step ABA (B @@@ Hole) id_sub ABA_in fact_term_eq_BA' fact_term_eq_BBA.

(* Two-step reduction A ->> B(B(A)) *)
Definition s_A_BBA : (A!) ->> (B @ B @ A!) := Cons s_A_BA p_BA_BBA.

(* B(B(...(A)...)) with n applications of B *)
Fixpoint nB_A (n : nat) : term :=
  match n with
  | 0   => A!
  | S n => B @ (nB_A n)
  end.

(* B(B(...(Hole)...)) with n applications of B *)
Fixpoint nB_Hole (n : nat) : context :=
  match n with
  | 0   => Hole
  | S n => B @@@ (nB_Hole n)
  end.

Lemma fact_term_eq_nBA :
  forall n,
    fill (nB_Hole n) (@Fun F X A (vmap (substitute id_sub) (vnil fterm))) [=]
    nB_A n.
Proof.
induction n as [| n IH]; simpl; intro m; destruct m; constructor; intro i.
contradiction (vnil False).
dependent destruction i.
apply IH.
contradiction (vnil False).
Qed.

Lemma fact_term_eq_BnBA :
  forall n,
    fill (nB_Hole n) (@Fun F X B (vmap (substitute id_sub) (vcons (A !!) (vnil fterm)))) [=]
    (B @ nB_A n).
Proof.
induction n as [| n IH]; simpl; intro m.
apply fact_term_eq_BA.
destruct m; constructor.
intro i.
dependent destruction i.
apply IH.
contradiction (vnil False).
Qed.

(* Step B(B(...(A)...)) -> B(B(B(...(A)...))) with n applications of B at left side *)
Definition p_nBA_nBBA (n : nat) : (nB_A n) [>] (B @ (nB_A n)) := Step ABA (nB_Hole n) id_sub ABA_in (fact_term_eq_nBA n) (fact_term_eq_BnBA n).

(* n-step reduction A -1-> B(A) -2-> B(B(A)) -3-> ... -n-> B(B(B(...(A)...))) with n applications of B at right side *)
Fixpoint s_A_nBA (n : nat) : (A!) ->> (nB_A n) :=
  match n as m in nat return (A!) ->> (nB_A m) with
  | 0   => Nil (A!)
  | S n => Cons (s_A_nBA n) (p_nBA_nBBA n)
  end.

(* s_A_nBA but with Sigma return type including right-most term *)
Definition limit_s_A_nBA (n : nat) : {t : term & (A!) ->> t} :=
  existT (fun (t : term) => (A!) ->> t) (nB_A n) (s_A_nBA n).

(* Omega-step reduction A -1-> B(A) -2-> B(B(A)) -3-> ... B(B(B(...))) *)
Definition s_A_repeat_B : (A!) ->> repeat_B :=
  Lim repeat_B limit_s_A_nBA.

(* Ugly notation *)
Notation "| s |" := (projT2 s) (no associativity, at level 75).
Notation "$ s $" := (projT1 s) (no associativity, at level 75).

(* This reduction is 'good' *)
Lemma good_s_A_repeat_B :
  good s_A_repeat_B.
Proof.
split.
induction n; simpl; trivial.
intros n m H.
induction H; simpl.
exists (inl _ tt).
apply embed_refl.
destruct IHle as [i IH].
exists (inr _ i).
assumption.
Qed.

(*
Lemma sfdsf :
  forall (n : nat) (i : pref_type (s_A_nBA (S n))),
    ($ pref (s_A_nBA (S n)) i $) = (B @ ($ pref (s_A_nBA n) i $)).
*)

(* This reduction is weakly convergent *)
(* TODO: generalize proofs like these as much as possible in the general theory *)
Lemma weakly_convergent_s_A_repeat_B :
  weakly_convergent s_A_repeat_B.
Proof.
split.
exact good_s_A_repeat_B.
split; simpl.
induction n.
simpl; split; constructor.
split.
simpl.
admit. (* by IHn *)
assumption.

intro d.
exists (existT (fun n:nat => pref_type (s_A_nBA n)) (S d) (inl _ tt)); simpl.

induction d.
constructor.
intros [n i] H.
(* we have to look one step further back than i here *)
assert (IH := IHd (existT (fun n:nat => pref_type (s_A_nBA n)) n i) (embed_cons_left H)); clear IHd.
admit.

(*
split.
exact good_s_A_repeat_B.
split; simpl.
admit. (* by induction on n *)
intro d.
exists (existT (fun n:nat => pref_type (s_A_nBA n)) (S d) (inl _ tt)).
intros j H.
*)
(*
induction H.
induction d.
apply teut_0.
assert (A1 : repeat_B = (B @ repeat_B)).
admit. (* Rewrite term_bis equality *)
rewrite A1.
assert (j : pref_type (s_A_nBA (S d))).
admit. (* Assume we have the 'right' one, i.e. equivalent of i *)
assert (A2 : ($ pref (s_A_nBA (S (S d))) i $) = (B @ ($ pref (s_A_nBA (S d)) j $))).
admit. (* This should be easy, assuming the right j *)
rewrite A2.
apply teut_fun.
intro i0.
dependent destruction i0.
apply IHd.
admit. (* This should somehow follow from what j is *)
dependent destruction i0.
admit. (* Maybe induction H1; induction d was not the right choice *)
*)
Admitted.

(* This reduction is weakly convergent *)
Lemma strongly_convergent_s_A_repeat_B :
  strongly_convergent s_A_repeat_B.
Proof.
Admitted.

Open Scope ord'_scope.

(* Compression lemma is meaningless for this reduction, but
   maybe we should show just that. *)
Lemma length_s_A_repeat_B_le_omega :
  length s_A_repeat_B <=' Omega.
Proof.
simpl.
constructor.
intro n.
apply ord'_le_pred_right with (existT (fun (n : nat) => pred_type n) (S n) (inl _ tt)).
simpl.
induction n as [| n IH]; simpl.
constructor.
apply Ord'_le_Succ with (inl (pred_type n) tt).
assumption.
Qed.

(* Let's also show the other direction *)
Lemma omega_le_length_s_A_repeat_B :
  Omega <=' length s_A_repeat_B.
Proof.
simpl.
constructor.
intro n.
apply ord'_le_pred_right with (existT (fun (n : nat) => pred_type (length (s_A_nBA n))) (S n) (inl _ tt)).
simpl.
induction n as [| n IH]; simpl.
constructor.
apply Ord'_le_Succ with (inl (pred_type (length (s_A_nBA n))) tt).
assumption.
Qed.

(* Just because both directions are so similar *)
Lemma length_s_A_repeat_B_eq_omega :
  length s_A_repeat_B ==' Omega.
Proof.
split; simpl;
  constructor;
  intro n;
  [ apply ord'_le_pred_right with (existT (fun (n : nat) => pred_type n) (S n) (inl _ tt))
  | apply ord'_le_pred_right with (existT (fun (n : nat) => pred_type (length (s_A_nBA n))) (S n) (inl _ tt)) ];
  induction n as [| n IH]; simpl;
  [ constructor
  | apply Ord'_le_Succ with (inl (pred_type n) tt); assumption
  | constructor
  | apply Ord'_le_Succ with (inl (pred_type (length (s_A_nBA n))) tt); assumption ].
Qed.