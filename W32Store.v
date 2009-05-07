Require Import Arith.
Require Import Word32.
Require Import Memory.

Module W32S <: STORE.
  Definition location := nat.
  Definition value := w32.

  Definition eq := eq_nat.

  Definition location_eq_dec := eq_nat_dec.
End W32S.
