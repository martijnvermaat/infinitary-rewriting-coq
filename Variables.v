(*
  A decidable set of variables.
*)
Record Variables : Type := mkVariables {
  variable :> Type;
  beq_var : variable -> variable -> bool;
  beq_var_ok : forall x y, beq_var x y = true <-> x = y
}.

Implicit Arguments mkVariables [variable beq_var].
Implicit Arguments beq_var [v].
Implicit Arguments beq_var_ok [v x y].
