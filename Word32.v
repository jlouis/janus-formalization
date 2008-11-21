(* Formalization of 32-bit Integers. Heavily inspired by the CompCert project,
   {http://compcert.inria.fr}, Xavier Leroy et al. *)

Require Import BaseLib.

Open Scope Z_scope.

Definition word_size : nat := 32%nat.
Definition modulus : Z := two_power_nat word_size.
Definition half_modulus : Z := modulus / 2.

(* The following sets up some basic inductive types to compare W32's *)

Inductive comparison : Set :=
| Ceq : comparison
| Cne : comparison
| Clt : comparison
| Cgt : comparison
| Cleq : comparison
| Cgeq : comparison.

Definition negate_comparison c : comparison :=
  match c with
    | Ceq => Cne
    | Cne => Ceq
    | Clt => Cgeq
    | Cleq => Cgt
    | Cgt => Cleq
    | Cgeq => Clt
  end.

Definition swap_comparison c : comparison :=
  match c with
    | Ceq => Ceq
    | Cne => Cne
    | Clt => Cgt
    | Cgt => Clt
    | Cleq => Cgeq
    | Cgeq => Cleq
  end.

(* A W32 is a 32-bit word. It is represented by a Coq integer [Z] and a proof
   it is within the allowed range *)

Record w32: Set := mkint { intval: Z; intrange: 0 <= intval < modulus }.

Module Word32.

Definition max_unsiged : Z := modulus -1.
Definition max_signed  : Z := half_modulus -1.
Definition min_signed  : Z := - half_modulus.

(* The following section embeds and projects traditional Coq integers [Z]
   inside w32 integers *)
Definition unsigned (n: w32) : Z := intval n.

Definition signed (n: w32) : Z :=
  if zlt (unsigned n) half_modulus
    then unsigned n
    else unsigned n - modulus.

End Word32.