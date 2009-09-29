CoInductive Stream (A : Set) : Set :=
| Cons : A -> Stream A -> Stream A.

Implicit Arguments Cons [A].

CoFixpoint repeat (A : Set) (a : A) : Stream A :=
  Cons a (repeat A a).

Implicit Arguments repeat [A].

Eval simpl in (repeat 3).

Definition head (A : Set) (s : Stream A) :=
  match s with Cons a s' => a end.

Implicit Arguments head [A].

Eval simpl in (head (Cons 4 (repeat 3))).

CoInductive Term : Set :=
| A : Term
| B : Term -> Term -> Term.

CoFixpoint build : Term :=
  B A build.

Check build.

Eval simpl in build.

Require Import Bvector.

CoInductive VTerm : Set :=
| Var : nat -> VTerm
| F : forall n : nat, vector VTerm n -> VTerm.

Check (Var 4).

Check (F 2 (Vcons VTerm (Var 3) 1 (Vcons VTerm (Var 7) 0 (Vnil VTerm)))).
