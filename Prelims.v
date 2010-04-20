Set Implicit Arguments.

Notation "!" := (False_rect _).

Definition S_eq : forall (n m : nat), n = m -> S n = S m :=
  fun n m H => f_equal S H.

(*
Definition S_eq_inv : forall (n m : nat), S n = S m -> n = m :=
  fun n m H => eq_add_S n m H.
*)

Definition S_eq_inv : forall (n m : nat), S n = S m -> n = m :=
  fun (n m : nat) (H : S n = S m) =>
  match (sym_eq H) in (_ = Sn) return pred Sn = pred (S m) with
  | refl_equal => refl_equal (pred (S m))
end.

Definition disc_O_S : forall (n : nat), O <> S n :=
  fun n H =>
  let P := (fun q : nat => match q with 0 => (False -> False) | S q => False end) in
  match H in (_ = q) return P q with refl_equal => (fun a => a) end.

Definition disc_S_O : forall (n : nat), S n <> O :=
  fun n H => disc_O_S (sym_eq H).


Require Import Bvector.

Implicit Arguments Vnil [A].
Implicit Arguments Vcons.
Implicit Arguments Vhead.
Implicit Arguments Vtail.
Implicit Arguments Vconst.

Section Vnth.

Variable A : Type. Notation vec := (vector A).

Require Import Program.

Program Fixpoint Vnth n (v : vec n) : forall i, i < n -> A :=
  match v with
  | Vnil =>
      fun i ip => False_rect _ _
  | Vcons x p v' =>
      fun i =>
        match i with
        | 0 => fun _ => x
          | S j => fun H => Vnth v' (i:=j) _
        end
  end.
Next Obligation.
dependent destruction ip.
Defined.
Next Obligation.
auto with *.
Defined.

End Vnth.

Section Vfolds.

Variable A : Type. Notation vec := (vector A).

(* Vfold_left f b [a1 .. an] = f .. (f (f b a1) a2) .. an *)

Fixpoint Vfold_left (B : Type) (f : B->A->B) (b:B) n (v : vec n)
  {struct v} : B :=
  match v with
    | Vnil => b
    | Vcons a _ w => f (Vfold_left f b w) a
  end.

(* Vfold_right f [a1 .. an] b = f a1 (f a2 .. (f an b) .. ) *)

Fixpoint Vfold_right (B : Type) (f : A->B->B) n (v : vec n) (b:B)
  {struct v} : B :=
  match v with
    | Vnil => b
    | Vcons a _ w => f a (Vfold_right f w b)
  end.

End Vfolds.

Section map.

Variables (A B : Type) (f : A->B).
Notation vecA := (vector A).
Notation vecB := (vector B).

Fixpoint Vmap n (v : vecA n) {struct v} : vecB n :=
  match v with
  | Vnil => Vnil
  | Vcons a _ v' => Vcons (f a) (Vmap v')
  end.

End map.

Section Vforall.

Variable A : Type. Notation vec := (vector A).
Variable P : A -> Prop.

Fixpoint Vforall n (v : vec n) { struct v } : Prop :=
  match v with
  | Vnil => True
  | Vcons a _ w => P a /\ Vforall w
  end.

End Vforall.

Section Vforall2_sec.

Variable A B : Type.

Notation vecA := (vector A).
Notation vecB := (vector B).

Variable R : A -> B -> Prop.

Fixpoint Vforall2n_aux n1 (v1 : vecA n1)
                       n2 (v2 : vecB n2) {struct v1} : Prop :=
  match v1, v2 with
    | Vnil, Vnil => True
    | Vcons a _ v, Vcons b _ w => R a b /\ Vforall2n_aux v w
    | _, _ => False
  end.

Definition Vforall2n n (v1 : vecA n) (v2 : vecB n) :=
  Vforall2n_aux v1 v2.

End Vforall2_sec.

Section Vapp.

Variable A : Type. Notation vec := (vector A).

Fixpoint Vapp n1 n2 (v1 : vec n1) (v2 : vec n2) {struct v1} : vec (n1+n2) :=
  match v1 with
  | Vnil => v2
  | Vcons a _ v' => Vcons a (Vapp v' v2)
  end.

End Vapp.

Section Vcast.

Variable A : Type. Notation vec := (vector A).

Program Fixpoint Vcast m (v : vec m) n (mn : m = n) {struct v} : vec n :=
  match v with
  | Vnil =>
      match n with
      | 0 => Vnil
      | _ => False_rect _ _
      end
  | Vcons x m' v' =>
      match n with
      | 0 => False_rect _ _
      | S n' => Vcons x (Vcast v' _)
      end
  end.

End Vcast.
