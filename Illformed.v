(*
  Terms with positions of transfinite length are ill-formed.
*)


Require Import Term.


(*
  Signature for terms with a binary function symbol 'app'.
*)
Module AppSignature <: Signature.

  Inductive symbol' : Set := app.
  Definition symbol := symbol'.

  Lemma eq_symbol_dec : forall f1 f2 : symbol, {f1 = f2} + {f1 <> f2}.
  Proof.
    intros; decide equality.
  Qed.

  Definition arity (f : symbol) : nat := 2.

End AppSignature.


(* Terms over 'app' and variables *)
Module App := Term.Term AppSignature NatVars.

Import App.
Import AppSignature.

Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].

(* Some terms *)
Check (Fun app (Vcons (Fun app (Vcons (Var 2) (Vcons (Var 3) Vnil))) (Vcons (Var 1) Vnil))).
Check (Var 3).

(*
  app(x,app(x,app(x,app(x,app(x,...)))))

     @
    / \
   x   @
      / \
     x   @
        / \
       x  ...
*)
CoFixpoint repeat_down : term :=
  Fun app (Vcons (Var 1) (Vcons repeat_down Vnil)).

Check repeat_down.

(*
  ...app(app(app(app(x,x),x),x),x)...

          ...
          /
         @
        / \
       @   x
      / \
     @   x
    / \
   x   x
*)
(*
CoFixpoint repeat_up (sub : term) : term :=
  repeat_up (Fun app (Vcons sub (Vcons (Var 1) Vnil))).

Check (repeat_up (Var 1)).
*)

(* Test the head of a term *)
Definition head (t : term) : nat :=
  match t with
  | Var n   => n
  | Fun _ _ => 1005
  end.

Eval simpl in (head (Fun app (Vcons (Fun app (Vcons (Var 2) (Vcons (Var 3) Vnil))) (Vcons (Var 1) Vnil)))).
Eval simpl in (head (Var 3)).
Eval simpl in (head repeat_down).
