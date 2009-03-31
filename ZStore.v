Require Import ZArith.
Require Import Memory.

(* Stores with integers as their base *)
Module ZS <: STORE.
  Definition location := nat.
  Definition value := Z.

  Definition eq := eq_nat.

  Definition location_eq_dec := eq_nat_dec.
End ZS.

