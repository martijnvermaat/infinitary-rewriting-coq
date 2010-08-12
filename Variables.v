(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines sets of variables.

   Equality of variables in the set must be decidable. *)

Record variables : Type := Variables {
  variable :> Type;
  beq_var : variable -> variable -> bool;
  beq_var_ok : forall x y, beq_var x y = true <-> x = y
}.

Implicit Arguments Variables [variable beq_var].
Implicit Arguments beq_var [v].
Implicit Arguments beq_var_ok [v x y].
