(*
  Trying to find a minimal test-case where dependent destruction fails.

  The definitions do not make any sense. The point of the test lemma is not
  to prove it, but to show that dependent destruction on the hypothesis fails.

  See also
  http://logical.saclay.inria.fr/coq-puma/messages/b650bcf7a740dfd2
*)


Require Import Equality.


Set Implicit Arguments.


Inductive s : nat -> Type :=
  | C : forall n (r : s n) m, s m.

Fixpoint pf n (r : s n) {struct r} : nat := n.

Inductive le : forall n (r : s n) m (q : s m), Prop :=
  | le_C : forall m (q : s m) (r : s (pf q)),
             le (C r m) q.

Lemma test1 :
  forall n (r : s n) m (q : s n),
    le (C r m) q -> n = m.
Proof.
intros n r m q H.
(*
   At this point, we would like to use dependent destruction on H, but it
   fails because the underlying simplify_one_dep_elim cycles.
   So we try to do it manually.
*)
(* dependent destruction H. *)
generalize_eqs H.
destruct H.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
(* ... *)
Admitted.

(* Let's try again *)

Lemma test2 :
  forall n (r : s n) m (q : s n),
    le (C r m) q -> n = m.
Proof.
intros n r m q H.
generalize_eqs H.
destruct H.
(*
   Here we can save the proof by destructing q. The point is that (pf q)
   then simplifies to m.
*)
destruct q.
simplify_one_dep_elim.
simplify_one_dep_elim.
simplify_one_dep_elim.
reflexivity.
Qed.
