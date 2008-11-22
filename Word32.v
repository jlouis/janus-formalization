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

(* Helper, provides division with rounding *)
Definition Zdiv_round (x y: Z) : Z :=
  if zlt x 0
    then if zlt y 0 then (-x) / (-y) else - ((-x) / y)
    else if zlt y 0 then -(x / (-y)) else x / y.

Definition Zmod_round (x y: Z) : Z :=
  x - (Zdiv_round x y) * y.

Definition divs (x y: w32) : w32 :=
  repr (Zdiv_round (signed x) (signed y)).

Definition mods (x y: w32) : w32 :=
  repr (Zmod_round (signed x) (signed y)).

Definition divu (x y: w32) : w32 :=
  repr (Zdiv_round (unsigned x) (unsigned y)).

Definition modu (x y: w32) : w32 :=
  repr (Zmod_round (unsigned x) (unsigned y)).

Definition fracprodu (x y: w32) : w32 :=
  repr (Zdiv_round ((unsigned x) * (unsigned y)) modulus).

(* Bitwise operations:

   We convert between Coq integers [Z] and their bit-level representations.
   this is done by representing the bit-level representation as a
   characteristic function of type [Z -> bool]. That is, an application [f i]
   tells the value of the [i]th bit. We ignore values greater than the 32th
   bit. *)

(* Shift and add a bool to a number *)
Definition Z_shift_add (b: bool) (x: Z) :=
  if b then 2 * x + 1 else 2 * x.

(* Decompose an integer [x] into its first bit and the rest
   by inspection of the [Z]-representation in Coq *)
Definition Z_bin_decomp (x: Z) : bool * Z :=
  match x with
    | Z0 => (false, 0)
    | Zpos p => (* Positive *)
      match p with
        | xI q => (true, Zpos q)
        | xO q => (false, Zpos q)
        | xH => (true, 0)
      end
    | Zneg p => (* Negative *)
      match p with
        | xI q => (true, Zneg q - 1)
        | xO q => (false, Zneg q)
        | xH => (true, -1)
      end
  end.

Fixpoint bits_of_Z (n: nat) (x: Z) {struct n}: Z -> bool :=
  match n with
    | O =>
      (fun i: Z => false)
    | S m =>
      let (b, y) := Z_bin_decomp x in
      let f := bits_of_Z m y in
        (fun i: Z => if zeq i 0 then b else f (i - 1))
  end.

Fixpoint Z_of_bits (n: nat) (f: Z -> bool) {struct n}: Z :=
  match n with
    | O => 0
    | S m => Z_shift_add (f 0) (Z_of_bits m (fun i => f (i + 1)))
end.

(* Bitwise logical ``and'', ``or'' and ``xor'' operations now follow
   easily *)
Definition bitwise_binop (f: bool -> bool -> bool) (x y: w32) :=
  let fx := bits_of_Z word_size (unsigned x) in
  let fy := bits_of_Z word_size (unsigned y) in
    repr (Z_of_bits word_size (fun i => f (fx i) (fy i))).

Definition and (x y: w32): w32 := bitwise_binop andb x y.
Definition or  (x y: w32): w32 := bitwise_binop orb  x y.
Definition xor (x y: w32): w32 := bitwise_binop xorb x y.

Definition not (x: w32): w32 := xor x mone.


(* Boolean predicates. These follow a C-like convention of everything
   different from zero is true.  *)
Definition is_false (x: w32) : Prop := x = zero.
Definition is_true  (x: w32) : Prop := x <> zero.

End Word32.