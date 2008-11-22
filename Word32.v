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

Lemma mod_in_range:
  forall x, 0 <= Zmod x modulus < modulus.
  intros.
  exact (Z_mod_lt x modulus (two_power_nat_pos word_size)).
Qed.

Definition repr (x: Z) : w32 :=
  mkint (Zmod x modulus) (mod_in_range x).

Definition zero := repr 0.
Definition one := repr 1.
Definition mone := repr (-1).

Lemma mkint_eq: forall x y Px Py,
  x = y -> mkint x Px = mkint y Py.
  intros. subst y.
  generalize (proof_irrelevance _ Px Py); intros.
  subst Py. reflexivity.
Qed.

(* We can decide equality for w32's *)
Lemma eq_dec: forall (x y: w32), {x = y} + {x <> y}.
  intros. destruct x. destruct y. case (zeq intval0 intval1); intro.
  left. apply mkint_eq. auto.
  right. red. intro. injection H. exact n.
Qed.

(* Arithmetic and logical operations over w32's *)
Definition eq (x y: w32) : bool :=
  if zeq (unsigned x) (unsigned y) then true else false.
Definition lt (x y: w32) : bool :=
  if zlt (signed x) (signed y) then true else false.
Definition ltu (x y: w32) : bool :=
  if zlt (unsigned x) (unsigned y) then true else false.

Definition neg (x: w32) : w32 :=
  repr (- unsigned x).

Definition cast8signed (x: w32) : w32 :=
  let y := Zmod (unsigned x) 256 in
    if zlt y 128 then repr y else repr (y - 256).

Definition cast8unsigned (x: w32) : w32 :=
    repr (Zmod (unsigned x) 256).

Definition cast16signed (x: w32) : w32 :=
  let y := Zmod (unsigned x) 65536 in
    if zlt y 32768 then repr y else repr (y - 65536).

Definition cast16unsigned (x: w32) : w32 :=
  repr (Zmod (unsigned x) 65536).

Definition add (x y: w32) : w32 :=
  repr (unsigned x + unsigned y).

Definition sub (x y: w32) : w32 :=
  repr (unsigned x - unsigned y).

Definition mul (x y: w32) : w32 :=
  repr (unsigned x * unsigned y).

End Word32.