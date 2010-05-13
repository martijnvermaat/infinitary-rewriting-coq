Require Import Rewriting.
Require Import Equality.

Set Implicit Arguments.

(*
  We construct the weakly orthogonal TRS with rules

    PS : P(S(x)) -> x
    SP : S(P(x)) -> x

  and show it is a counterexample to UN-inf.
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

(* U(U(U(...))) *)
CoFixpoint repeat_U : term :=
  U @ repeat_U.

(* D(D(D(...))) *)
CoFixpoint repeat_D : term :=
  D @ repeat_D.

(* D(U(D(U(...)))) *)
(* TODO: better to define repeat_DU and repeat_UD together? *)
CoFixpoint repeat_DU : term :=
  D @ U @ repeat_DU.

(* U(U(U(...t...))) *)
Fixpoint Unt (n : nat) t :=
  match n with
  | O   => t
  | S n => U @ (Unt n t)
  end.

(* D(D(D(...t...))) *)
Fixpoint Dnt (n : nat) t :=
  match n with
  | O   => t
  | S n => D @ (Dnt n t)
  end.

(* U(U(U(...t...))) *)
Fixpoint U2nt (n : nat) t :=
  match n with
  | O   => t
  | S n => U @ U @ (U2nt n t)
  end.

(* D(D(D(...t...))) *)
Fixpoint D2nt (n : nat) t :=
  match n with
  | O   => t
  | S n => D @ D @ (D2nt n t)
  end.

(* D^n @ U^n @ t *)
Definition DnUnt n t : term :=
  Dnt n (Unt n t).

(* U^n @ D^n @ t *)
Definition UnDnt n t : term :=
  Unt n (Dnt n t).

(* D^2n @ U^2n @ t *)
Definition D2nU2nt n t : term :=
  D2nt n (U2nt n t).

(* U^2n @ D^2n @ t *)
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

(* D(U(U(D(D(D(U(U(U(U(...)))))))))) *)
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

Definition psi := psi' 0.

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

Lemma hmmmm :
  forall n,
    psi' n [~] oldpsi' (2 * n).
Proof.
(* should be somehow possible to show, using lemma zo *)
Admitted.

Lemma oldpsin_eq_DSnUSnUoldpsiSSn :
  forall n,
    oldpsi' n = DnUnt (S n) (U @ (oldpsi' (S (S n)))).
Proof.
intro n.
rewrite (peek_eq (oldpsi' n)).
simpl.
generalize (oldpsi' (S (S n))).
induction n; intro t.
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
       match d with
       | 0 =>
           (cofix USnt (u : nat) : term :=
              match u with
              | 0 => U @ t
              | S u0 => U @ USnt u0
              end) 1
       | S d0 => D @ Dnt d0
       end) 0)).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
                 match u with
                 | 0 => U @ t
                 | S u0 => U @ USnt u0
                 end) 1)).
rewrite DSnUSnt_eq_DDnUnUt.
unfold DnUnt.
simpl.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
       match u with
       | 0 => U @ t
       | S u0 => U @ USnt u0
       end) 0)).
simpl.
reflexivity.
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
       match d with
       | 0 =>
           (cofix USnt (u : nat) : term :=
              match u with
              | 0 => U @ t
              | S u0 => U @ USnt u0
              end) (S (S n))
       | S d0 => D @ Dnt d0
       end) (S n))).
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
                 match u with
                 | 0 => U @ t
                 | S u0 => U @ USnt u0
                 end) (S (S n)))).
rewrite DSnUSnt_eq_DDnUnUt.
simpl.
rewrite UUSnt_eq_USnUt with (S n) (U @ t).
rewrite IHn with (U @ t).
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

(* D(D(D(...))) is infinite *)
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

(* D(D(D(...))) is a normal form *)
Lemma nf_D :
  normal_form (system := UNWO_trs) repeat_D.
Proof.
(* TODO: a lot of this proof is a mess, cleanup
   Also, I expect that this could be generalized and shortened quite a bit
   by using pos_eq. *)
intros [c [r [u [H1 H2]]]].
destruct H1 as [H1 | H1].
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

admit. (* same argument as above for r=UD instead of r=DU *)
Admitted.

(* U(U(U(...))) is a normal form *)
Lemma nf_U :
  normal_form (system := UNWO_trs) repeat_U.
Proof.
Admitted.

(* D(D(D(...))) is an infinite normal form *)
Lemma infinite_nf_D :
  infinite repeat_D /\ normal_form (system := UNWO_trs) repeat_D.
Proof.
exact (conj infinite_D nf_D).
Qed.

(* U(U(U(...))) is an infinite normal form *)
Lemma infinite_nf_U :
  infinite repeat_U /\ normal_form (system := UNWO_trs) repeat_U.
Proof.
Admitted.

(* D(D(D(...))) and U(U(U(...))) are different *)
Lemma neq_D_U :
  ~ repeat_D [~] repeat_U.
Proof.
intro H.
rewrite (peek_eq repeat_D), (peek_eq repeat_U) in H.
inversion H.
Qed.

(* D(D(D(...))) and U(U(U(...))) are the only infinite normal forms *)
Lemma only_infinite_nf_D_U :
  forall t,
    infinite t /\ normal_form (system := UNWO_trs) t ->
    t [~] repeat_D \/ t [~] repeat_U.
Proof.
(* We should be able to prove this, but it's probably a lot of work *)
intros [x | [] args] [It Nt].

destruct (It 1) as [p [Dp Hp]].
contradict Hp.
destruct p as [| a [| b p]].
discriminate Dp.
reflexivity.
discriminate Dp.

left.
admit.

right.
admit.
Admitted.

(* Reductions *)
Notation Step := (Step UNWO_trs).
Notation Nil := (Nil UNWO_trs).

Notation "s [>] t" := (step UNWO_trs s t) (at level 40).
Notation "s ->> t" := (sequence UNWO_trs s t) (at level 40).

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

Generalizable All Variables.

(* D(U(D(U(...)))) rewrites only to itself *)
Lemma rewrites_to_itself_DU :
  forall `(p : repeat_DU [>] t),
    t [~] repeat_DU.
Proof.
intros s p.
dependent destruction p.
destruct i as [H | [H | H]]; try (rewrite <- H in t1, t0; clear H).

unfold DU, lhs, DU_l in t0.
unfold DU, rhs, DU_r in t1.
apply term_bis_trans with (fill c (substitute u (1 !))).
exact (term_bis_symm t1).
clear t1.
induction c as [| f i j e v c IH w]; simpl in t0 |- *.

(* This does not seem to be the right way, we cannot prove the induction step *)

(* from t0 deduce u 1 [=] repeat_DU, then transitivity of [=] *)
apply term_eq_implies_term_bis.
intro n.
assert (H := (term_bis_implies_term_eq t0) (S (S n))).
rewrite (peek_eq repeat_DU) in H.
dependent destruction H.
assert (H1 := H First).
dependent destruction H1.
assert (H2 := H0 First).
rewrite (peek_eq repeat_DU) in H2.
dependent destruction H2.
constructor.
unfold vmap in x; simpl in x.
rewrite <- x.
rewrite (peek_eq repeat_DU).
simpl.
constructor.
assumption.

(*apply IH; clear IH.*)
admit. (* more work *)

admit. (* same as previous case *)

contradict H.
Qed.

(* Zero-step reduction psi ->> psi *)
Definition s_oldpsi0_oldpsi0 : oldpsi' 0 ->> oldpsi' 0 := Nil (oldpsi' 0).
Definition s_psi0_psi0 : psi' 0 ->> psi' 0 := Nil (psi' 0).

(* Substitution for step psi' 0 -> U @ psi' 2 *)
Definition sub_oldpsi0_Uoldpsi2 (x : X) : term :=
  match x with
  | 1 => U @ oldpsi' 2
  | _ => Var x
  end.

Definition sub_psi0_Upsi1 (x : X) : term :=
  match x with
  | 1 => U @ psi' 1
  | _ => Var x
  end.

Lemma fact_term_bis_oldpsi0 :
  fill Hole (substitute sub_oldpsi0_Uoldpsi2 (lhs DU)) [~] oldpsi' 0.
Proof.
rewrite (peek_eq (oldpsi' 0)).
simpl.
constructor.
intro i; simpl in i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
(* this is really annoying, but i guess there's no way around it... *)
rewrite (peek_eq ((cofix Dnt (d : nat) : term :=
         match d with
         | 0 =>
             (cofix USnt (u : nat) : term :=
               match u with
                 | 0 => U @ oldpsi' 2
                   | S u0 => U @ USnt u0
                     end) 1
         | S d0 => D @ Dnt d0
         end) 0)).
simpl.
rewrite (peek_eq ((cofix USnt (u : nat) : term :=
         match u with
         | 0 => U @ oldpsi' 2
            | S u0 => U @ USnt u0
               end) 0)).
simpl.
constructor.
unfold vmap.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
apply term_bis_refl.
Qed.

Lemma fact_term_bis_psi0 :
  fill Hole (substitute sub_psi0_Upsi1 (lhs DU)) [~] psi' 0.
Proof.
rewrite (peek_eq (psi' 0)).
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

(* Step psi' 0 -> U @ psi' 2 *)
Definition p_oldpsi0_Uoldpsi2 : oldpsi' 0 [>] (U @ oldpsi' 2) :=
  Step DU Hole sub_oldpsi0_Uoldpsi2 DU_in fact_term_bis_oldpsi0 (term_bis_refl (U @ oldpsi' 2)).

Definition p_psi0_Upsi1 : psi' 0 [>] (U @ psi' 1) :=
  Step DU Hole sub_psi0_Upsi1 DU_in fact_term_bis_psi0 (term_bis_refl (U @ psi' 1)).

(* Single-step reduction psi' 0 ->> U @ psi' 2 *)
Definition s_oldpsi0_Uoldpsi2 : oldpsi' 0 ->> (U @ oldpsi' 2) :=
  Cons s_oldpsi0_oldpsi0 p_oldpsi0_Uoldpsi2.

Definition s_psi0_Upsi1 : psi' 0 ->> (U @ psi' 1) :=
  Cons s_psi0_psi0 p_psi0_Upsi1.

(* Substitution for step U @ psi' 2 -> U D D U U U @ psi' 4 *)
Definition sub_Uoldpsi2_UDDUUUoldpsi4 (x : X) : term :=
  match x with
  | 1 => U @ U @ U @ oldpsi' 4
  | _ => Var x
  end.

Definition sub_Upsi1_UDDUUUpsi2 (x : X) : term :=
  match x with
  | 1 => U @ U @ U @ psi' 2
  | _ => Var x
  end.

Lemma fact_term_bis_Uoldpsi2 :
  fill (U @@@ D @@@ D @@@ Hole) (substitute sub_Uoldpsi2_UDDUUUoldpsi4 (lhs DU))
  [~]
  (U @ oldpsi' 2).
Proof.
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
rewrite (peek_eq (oldpsi' 2)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix SnD (d : nat) : term :=
         match d with
         | 0 =>
             (cofix SnU (u : nat) : term :=
                match u with
                | 0 => U @ oldpsi' 4
                | S u0 => U @ SnU u0
                end) 3
         | S d0 => D @ SnD d0
         end) 2)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix SnD (d : nat) : term :=
         match d with
         | 0 =>
             (cofix SnU (u : nat) : term :=
                match u with
                | 0 => U @ oldpsi' 4
                | S u0 => U @ SnU u0
                end) 3
         | S d0 => D @ SnD d0
         end) 1)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
rewrite (peek_eq ((cofix SnD (d : nat) : term :=
         match d with
         | 0 =>
             (cofix SnU (u : nat) : term :=
                match u with
                | 0 => U @ oldpsi' 4
                | S u0 => U @ SnU u0
                end) 3
         | S d0 => D @ SnD d0
         end) 0)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
unfold vmap.
simpl.
rewrite (peek_eq ((cofix SnU (u : nat) : term :=
         match u with
         | 0 => U @ oldpsi' 4
         | S u0 => U @ SnU u0
         end) 2)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix SnU (u : nat) : term :=
         match u with
         | 0 => U @ oldpsi' 4
         | S u0 => U @ SnU u0
         end) 1)).
simpl.
constructor.
intro i.
dependent destruction i; [idtac | inversion i].
simpl.
rewrite (peek_eq ((cofix SnU (u : nat) : term :=
         match u with
         | 0 => U @ oldpsi' 4
         | S u0 => U @ SnU u0
         end) 0)).
simpl.
apply term_bis_refl.
Qed.

(* TODO: rewrite this for new psi' *)
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

(* Step U @ psi' 2 -> U D D U U U @ psi' 4 *)
Definition p_Uoldpsi2_UDDUUUoldpsi4 : (U @ oldpsi' 2) [>] (U @ D @ D @ U @ U @ U @ oldpsi' 4) :=
  Step DU (U @@@ D @@@ D @@@ Hole) sub_Uoldpsi2_UDDUUUoldpsi4 DU_in fact_term_bis_Uoldpsi2 (term_bis_refl (U @ D @ D @ U @ U @ U @ oldpsi' 4)).

Definition p_Upsi1_UDDUUUpsi2 : (U @ psi' 1) [>] (U @ D @ D @ U @ U @ U @ psi' 2) :=
  Step DU (U @@@ D @@@ D @@@ Hole) sub_Upsi1_UDDUUUpsi2 DU_in fact_term_bis_Upsi1 (term_bis_refl (U @ D @ D @ U @ U @ U @ psi' 2)).

(* Two-step reduction psi' 0 ->> U D D U U U @ psi' 4 *)
Definition s_oldpsi0_UDDUUUoldpsi4 : oldpsi' 0 ->> (U @ D @ D @ U @ U @ U @ oldpsi' 4) := Cons s_oldpsi0_Uoldpsi2 p_Uoldpsi2_UDDUUUoldpsi4.

Definition s_psi0_UDDUUUpsi2 : psi' 0 ->> (U @ D @ D @ U @ U @ U @ psi' 2) := Cons s_psi0_Upsi1 p_Upsi1_UDDUUUpsi2.

(* Substitution for step U D D U U U @ psi' 4 -> U D U U @ psi' 4 *)
Definition sub_UDDUUUoldpsi4_UDUUoldpsi4 (x : X) : term :=
  match x with
  | 1 => U @ U @ oldpsi' 4
  | _ => Var x
  end.

Definition sub_UDDUUUpsi2_UDUUpsi2 (x : X) : term :=
  match x with
  | 1 => U @ U @ psi' 2
  | _ => Var x
  end.

Lemma fact_term_bis_UDDUUUoldpsi4 :
  fill (U @@@ D @@@ Hole) (substitute sub_UDDUUUoldpsi4_UDUUoldpsi4 (lhs DU))
  [~]
  (U @ D @ D @ U @ U @ U @ oldpsi' 4).
Proof.
(* more of the same *)
Admitted.

Lemma fact_term_bis_UDDUUUpsi2 :
  fill (U @@@ D @@@ Hole) (substitute sub_UDDUUUpsi2_UDUUpsi2 (lhs DU))
  [~]
  (U @ D @ D @ U @ U @ U @ psi' 2).
Proof.
(* more of the same *)
Admitted.

(* Step U D D U U U @ psi' 4 -> U D U U @ psi' 4*)
Definition p_UDDUUUoldpsi4_UDUUoldpsi4 : (U @ D @ D @ U @ U @ U @ oldpsi' 4) [>] (U @ D @ U @ U @ oldpsi' 4) :=
  Step DU (U @@@ D @@@ Hole) sub_UDDUUUoldpsi4_UDUUoldpsi4 DU_in fact_term_bis_UDDUUUoldpsi4 (term_bis_refl (U @ D @ U @ U @ oldpsi' 4)).

Definition p_UDDUUUpsi2_UDUUpsi2 : (U @ D @ D @ U @ U @ U @ psi' 2) [>] (U @ D @ U @ U @ psi' 2) :=
  Step DU (U @@@ D @@@ Hole) sub_UDDUUUpsi2_UDUUpsi2 DU_in fact_term_bis_UDDUUUpsi2 (term_bis_refl (U @ D @ U @ U @ psi' 2)).

(* Three-step reduction psi' 0 ->> U D U U @ psi' 4 *)
Definition s_oldpsi0_UDUUoldpsi4 : oldpsi' 0 ->> (U @ D @ U @ U @ oldpsi' 4) := Cons s_oldpsi0_UDDUUUoldpsi4 p_UDDUUUoldpsi4_UDUUoldpsi4.

Definition s_psi0_UDUUpsi2 : psi' 0 ->> (U @ D @ U @ U @ psi' 2) := Cons s_psi0_UDDUUUpsi2 p_UDDUUUpsi2_UDUUpsi2.

(* Substitution for step U D U U @ psi' 4 -> U U @ psi' 4 *)
Definition sub_UDUUoldpsi4_UUoldpsi4 (x : X) : term :=
  match x with
  | 1 => U @ oldpsi' 4
  | _ => Var x
  end.

Definition sub_UDUUpsi2_UUpsi2 (x : X) : term :=
  match x with
  | 1 => U @ psi' 2
  | _ => Var x
  end.

Lemma fact_term_bis_UDUUoldpsi4 :
  fill (U @@@ Hole) (substitute sub_UDUUoldpsi4_UUoldpsi4 (lhs DU))
  [~]
  (U @ D @ U @ U @ oldpsi' 4).
Proof.
(* more of the same *)
Admitted.

Lemma fact_term_bis_UDUUpsi2 :
  fill (U @@@ Hole) (substitute sub_UDUUpsi2_UUpsi2 (lhs DU))
  [~]
  (U @ D @ U @ U @ psi' 2).
Proof.
(* more of the same *)
Admitted.

(* Step U D U U @ psi' 4 -> U U @ psi' 4*)
Definition p_UDUUoldpsi4_UUoldpsi4 : (U @ D @ U @ U @ oldpsi' 4) [>] (U @ U @ oldpsi' 4) :=
  Step DU (U @@@ Hole) sub_UDUUoldpsi4_UUoldpsi4 DU_in fact_term_bis_UDUUoldpsi4 (term_bis_refl (U @ U @ oldpsi' 4)).

Definition p_UDUUpsi2_UUpsi2 : (U @ D @ U @ U @ psi' 2) [>] (U @ U @ psi' 2) :=
  Step DU (U @@@ Hole) sub_UDUUpsi2_UUpsi2 DU_in fact_term_bis_UDUUpsi2 (term_bis_refl (U @ U @ psi' 2)).

(* Four-step reduction psi' 0 ->> U U @ psi' 4 *)
Definition s_oldpsi0_UUoldpsi4 : oldpsi' 0 ->> (U @ U @ oldpsi' 4) := Cons s_oldpsi0_UDUUoldpsi4 p_UDUUoldpsi4_UUoldpsi4.

Definition s_psi0_UUpsi2 : psi' 0 ->> (U @ U @ psi' 2) := Cons s_psi0_UDUUpsi2 p_UDUUpsi2_UUpsi2.

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

(* n-step reduction D^n @ U^n @ t -> t *)
Fixpoint s_DnUnt_t n t : DnUnt n t ->> t :=
  match n return DnUnt n t ->> t with
  | O   => Nil t
  | S n => snoc (p_DSnUSnt_DnUnt n t) (s_DnUnt_t n t)
  end.

(*
 psin_eq_DD2nU2nUUpsiSn :
 forall n, psi' n = (D @ D2nU2nt n (U @ U @ psi' (S n)))

Lemma psin_eq_DS2nUS2nUpsiSn :
  forall n,
    psi' n = DnUnt (S (2 * n)) (U @ (psi' (S n))).
*)

(* n-step reduction psi n -> U @ psi (S n) *)
(* TODO: would it be better to write this without program? *)
Program Definition s_oldpsin_UoldpsiSSn n : oldpsi' n ->> (U @ (oldpsi' (S (S n)))) :=
  s_DnUnt_t (S n) (U @ oldpsi' (S (S n))).
Next Obligation.
symmetry.
apply oldpsin_eq_DSnUSnUoldpsiSSn.
Defined.

Program Definition s_psin_UpsiSn n : psi' n ->> (U @ (psi' (S n))) :=
  s_DnUnt_t (S (2 * n)) (U @ psi' (S n)).
Next Obligation.
symmetry.
apply psin_eq_DS2nUS2nUpsiSn.
Defined.

(* Now we slightly adjust these sequences to take place under U^m *)

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

(* n-step reduction U^m @ D^n @ U^n @ t -> U^m t *)
Fixpoint s_UmDnUnt_Umt m n t : Unt m (DnUnt n t) ->> Unt m t :=
  match n return Unt m (DnUnt n t) ->> Unt m t with
  | O   => Nil (Unt m t)
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
Show Proof.
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
Fixpoint s_psi0_Unpsin n : psi' 0 ->> Unt n (psi' n) :=
  match n return psi' 0 ->> Unt n (psi' n) with
  | O   => Nil (psi' 0)
  | S n => append (s_psi0_Unpsin n) (s_Unpsin_USnpsiSn n)
  end.

(* psi rewrites to repeat_U *)
Definition s_psi_U : psi ->> repeat_U.
Admitted.

(* psi rewrites to repeat_D *)
Definition s_psi_D : psi ->> repeat_D.
Admitted.

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
exact s_psi_D.
exact s_psi_U.
exact nf_D.
exact nf_U.
Qed.

(* I think we don't need the norm function *)

Require Import ZArith.
Delimit Scope Int_scope with I.

Fixpoint sum (n : nat) (t : term) : Z :=
  match n with
  | 0   => Z0
  | S n => match t with
           | Var _      => Z0
           | Fun D args => vfold (-1)%Z Zplus (vmap (sum n) args)
           | Fun U args => vfold (1)%Z  Zplus (vmap (sum n) args)
           end
  end.

(*
Fixpoint fsum (t : fterm) : Z :=
  match t with
  | FVar _      => Z0
  | FFun D args => vfold (-1)%Z Zplus (vmap fsum args)
  | FFun U args => vfold (1)%Z  Zplus (vmap fsum args)
  end.
*)

(* I have no idea how to implement the norm functions *)
