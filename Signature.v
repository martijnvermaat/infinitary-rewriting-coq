(*
  A signature contains a decidable set of function symbols and
  an arity function on them.
*)


Record signature : Type := Signature {
  symbol :> Type;
  arity : symbol -> nat;
  beq_symb : symbol -> symbol -> bool;
  beq_symb_ok : forall x y, beq_symb x y = true <-> x = y
}.

Implicit Arguments Signature [symbol beq_symb].
Implicit Arguments arity [s].
Implicit Arguments beq_symb [s].
Implicit Arguments beq_symb_ok [s x y].
