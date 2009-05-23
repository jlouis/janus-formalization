(** Formalizations of integers modulo $2^32$ #2<sup>32</sup>#.
    Heavily inspired by the CompCert project,
    {http://compcert.inria.fr}, Xavier Leroy et al. *)

Require Import BaseLib.

Open Scope Z_scope.

Definition word_size : nat := 32%nat.
Definition modulus : Z := two_power_nat word_size.
Definition half_modulus : Z := modulus / 2.

(** The following sets up some basic inductive types to compare W32's *)

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

(** A W32 is a 32-bit word. It is represented by a Coq integer [Z] and a proof
   it is within the allowed range *)

Record w32: Set := mkint { intval: Z; intrange: 0 <= intval < modulus }.

Module Word32.

Definition max_unsigned : Z := modulus -1.
Definition max_signed  : Z := half_modulus -1.
Definition min_signed  : Z := - half_modulus.

(** The following section embeds and projects traditional Coq integers [Z]
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

(** We can decide equality for w32's *)

Lemma eq_dec: forall (x y: w32), {x = y} + {x <> y}.
  intros. destruct x. destruct y. case (zeq intval0 intval1); intro.
  left. apply mkint_eq. auto.
  right. red. intro. injection H. exact n.
Qed.

(** Arithmetic and logical operations over w32's *)

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

(** Helper, provides division with rounding *)

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

(** Bitwise operations:

   We convert between Coq integers [Z] and their bit-level representations.
   this is done by representing the bit-level representation as a
   characteristic function of type [Z -> bool]. That is, an application [f i]
   tells the value of the [i]th bit. We ignore values greater than the 32th
   bit. *)

(** Shift and add a bool to a number *)

Definition Z_shift_add (b: bool) (x: Z) :=
  if b then 2 * x + 1 else 2 * x.

(** Decompose an integer [x] into its first bit and the rest
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

(** Bitwise logical ``and'', ``or'' and ``xor'' operations now follow
   easily *)

Definition bitwise_binop (f: bool -> bool -> bool) (x y: w32) :=
  let fx := bits_of_Z word_size (unsigned x) in
  let fy := bits_of_Z word_size (unsigned y) in
    repr (Z_of_bits word_size (fun i => f (fx i) (fy i))).

Definition and (x y: w32): w32 := bitwise_binop andb x y.
Definition or  (x y: w32): w32 := bitwise_binop orb  x y.
Definition xor (x y: w32): w32 := bitwise_binop xorb x y.

Definition not (x: w32): w32 := xor x mone.

(** Compares *)

Definition cmp (c: comparison) (x y: w32) : bool :=
  match c with
    | Ceq => eq x y
    | Cne => negb (eq x y)
    | Clt => lt x y
    | Cleq => negb (lt y x)
    | Cgt => lt y x
    | Cgeq => negb (lt x y)
end.

Definition cmpu (c: comparison) (x y: w32) : bool :=
  match c with
    | Ceq => eq x y
    | Cne => negb (eq x y)
    | Clt => ltu x y
    | Cleq => negb (ltu y x)
    | Cgt => ltu y x
    | Cgeq => negb (ltu x y)
end.

(* Boolean predicates. These follow a C-like convention of everything
   different from zero is true.  *)

Definition is_false (x: w32) : Prop := x = zero.
Definition is_true  (x: w32) : Prop := x <> zero.

(** * Properties *)

(** ** Modular arithmetic *)

Section Eq_Modulo.
  Variable modul: Z.
  Hypothesis modul_pos: modul > 0.

  Definition eqmod (x y: Z) : Prop := exists k, x = k * modul + y.

  Lemma eqmod_refl:
    forall x, eqmod x x.
  Proof.
    intros; red. exists 0. omega.
  Qed.

  Lemma eqmod_refl2:
    forall x y, x = y -> eqmod x y.
  Proof.
    intros. subst y. apply eqmod_refl.
  Qed.

  Lemma eqmod_sym:
    forall x y, eqmod x y -> eqmod y x.
  Proof.
    intros x y [k EQ]; red. exists (-k). subst x. ring.
  Qed.

  Lemma eqmod_trans:
    forall x y z,
      eqmod x y -> eqmod y z -> eqmod x z.
  Proof.
    intros x y z [k1 EQ1] [k2 EQ2]; red.
    exists (k1 + k2). subst x; subst y. ring.
  Qed.

  Lemma eqmod_small_eq:
    forall x y, eqmod x y -> 0 <= x < modul -> 0 <= y < modul -> x = y.
  Proof.
    intros x y [k EQ] I1 I2.
    generalize (Zdiv_unique _ _ _ _ EQ I2). intro.
    rewrite (Zdiv_small x modul I1) in H. subst k. omega.
  Qed.

  Lemma eqmod_eq:
    forall x y, eqmod x y -> x mod modul = y mod modul.
  Proof.
    intros x y [k EQ]. subst x.
    rewrite Zplus_comm. apply Z_mod_plus. auto.
  Qed.

  Lemma eqmod_mod_eq:
    forall x y, eqmod x y -> x mod modul = y mod modul.
  Proof.
    intros x y [k EQ]. subst x.
    rewrite Zplus_comm. apply Z_mod_plus. trivial.
  Qed.

  Lemma eqmod_mod:
    forall x, eqmod x (x mod modul).
  Proof.
    intros; red. exists (x / modul).
    rewrite Zmult_comm. apply Z_div_mod_eq. trivial.
  Qed.

  Lemma eqmod_add:
    forall a b c d, eqmod a b -> eqmod c d -> eqmod (a + c) (b + d).
  Proof.
    intros a b c d [k1 EQ1] [k2 EQ2]; red.
    subst a; subst c. exists (k1 + k2). ring.
  Qed.

  Lemma eqmod_neg:
    forall x y, eqmod x y -> eqmod (-x) (-y).
  Proof.
    intros x y [k EQ1]; red. exists (-k). rewrite EQ1. ring.
  Qed.

  Lemma eqmod_sub:
    forall a b c d, eqmod a b -> eqmod c d -> eqmod (a - c) (b - d).
  Proof.
    intros a b c d [k1 EQ1] [k2 EQ2]; red.
    subst a; subst c; exists (k1 - k2). ring.
  Qed.

  Lemma eqmod_mult:
    forall a b c d, eqmod a c -> eqmod b d -> eqmod (a * b) (c * d).
  Proof.
    intros a b c d [k1 EQ1] [k2 EQ2]; red.
    subst a; subst b. exists (k1 * k2 * modul + c * k2 + k1 * d). ring.
  Qed.

End Eq_Modulo.

(** Specialization of modular arithmetic to the case $2^{32}$ we are working in *)

Lemma modulus_pos:
  modulus > 0.
Proof.
  unfold modulus. apply two_power_nat_pos.
Qed.
Hint Resolve modulus_pos: mortar.

Definition eqm := eqmod modulus.


Lemma eqm_refl: forall x, eqm x x.
Proof (eqmod_refl modulus).
Hint Resolve eqm_refl: mortar.

Lemma eqm_refl2:
  forall x y, x = y -> eqm x y.
Proof (eqmod_refl2 modulus).
Hint Resolve eqm_refl2: mortar.

Lemma eqm_sym: forall x y, eqm x y -> eqm y x.
Proof (eqmod_sym modulus).
Hint Resolve eqm_sym: mortar.

Lemma eqm_trans: forall x y z, eqm x y -> eqm y z -> eqm x z.
Proof (eqmod_trans modulus).
Hint Resolve eqm_trans: mortar.

Lemma eqm_samerepr:
  forall x y,
    eqm x y -> repr x = repr y.
Proof.
  intros. unfold repr. apply mkint_eq.
  apply eqmod_eq. auto with mortar. exact H.
Qed.

Lemma eqm_small_eq:
  forall x y, eqm x y -> 0 <= x < modulus -> 0 <= y < modulus -> x = y.
Proof (eqmod_small_eq modulus).
Hint Resolve eqm_small_eq: mortar.

Lemma eqm_add:
  forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof (eqmod_add modulus).
Hint Resolve eqm_add: mortar.

Lemma eqm_neg:
  forall x y, eqm x y -> eqm (-x) (-y).
Proof (eqmod_neg modulus).
Hint Resolve eqm_neg: mortar.

Lemma eqm_sub:
  forall a b c d, eqm a b -> eqm c d -> eqm (a - c) (b - d).
Proof (eqmod_sub modulus).
Hint Resolve eqm_sub: mortar.

Lemma eqm_mult:
  forall a b c d, eqm a c -> eqm b d -> eqm (a * b) (c * d).
Proof (eqmod_mult modulus).
Hint Resolve eqm_mult: mortar.

(** ** Coercions between [Z] and [w32] *)

Lemma eqm_unsigned_repr:
  forall z, eqm z (unsigned (repr z)).
Proof.
  unfold eqm, repr, unsigned; intros; simpl.
  apply eqmod_mod. auto with mortar.
Qed.
Hint Resolve eqm_unsigned_repr: mortar.

Lemma eqm_unsigned_repr_l:
  forall a b, eqm a b -> eqm (unsigned (repr a)) b.
Proof.
  intros. apply eqm_trans with a.
  apply eqm_sym. apply eqm_unsigned_repr. auto.
Qed.
Hint Resolve eqm_unsigned_repr_l: mortar.

Lemma eqm_unsigned_repr_r:
  forall a b, eqm a b -> eqm a (unsigned (repr b)).
Proof.
  intros. apply eqm_trans with b. auto.
  apply eqm_unsigned_repr.
Qed.
Hint Resolve eqm_unsigned_repr_r: mortar.

Lemma eqm_signed_unsigned:
  forall x, eqm (signed x) (unsigned x).
Proof.
  intro; red; unfold signed. set (y := unsigned x).
  case (zlt y half_modulus); intro.
  apply eqmod_refl. red; exists (-1); ring.
Qed.

Theorem unsigned_range:
  forall i, 0 <= unsigned i < modulus.
Proof.
  destruct i; simpl. auto.
Qed.
Hint Resolve unsigned_range: mortar.

Theorem unsigned_range_2:
  forall i, 0 <= unsigned i <= max_unsigned.
Proof.
  intro; unfold max_unsigned.
  generalize (unsigned_range i). omega.
Qed.
Hint Resolve unsigned_range_2: mortar.

Theorem signed_range:
  forall i, min_signed <= signed i <= max_signed.
Proof.
  intros. unfold signed.
  generalize (unsigned_range i). set (n := unsigned i). intros.
  case (zlt n half_modulus); intro.
  unfold max_signed. assert (min_signed < 0). compute. auto.
  omega.
  unfold min_signed, max_signed. change modulus with (2 * half_modulus).
  change modulus with (2 * half_modulus) in H. omega.
Qed.

Theorem repr_unsigned:
  forall i, repr (unsigned i) = i.
Proof.
  destruct i; simpl. unfold repr. apply mkint_eq.
  apply Zmod_small. trivial.
Qed.
Hint Resolve repr_unsigned: mortar.

Lemma repr_signed:
  forall i, repr (signed i) = i.
Proof.
  intros. transitivity (repr (unsigned i)).
  apply eqm_samerepr. apply eqm_signed_unsigned. auto with mortar.
Qed.
Hint Resolve repr_unsigned: mortar.

Theorem unsigned_repr:
  forall z, 0 <= z <= max_unsigned -> unsigned (repr z) = z.
Proof.
  intros. unfold repr, unsigned; simpl.
  apply Zmod_small. unfold max_unsigned in H. omega.
Qed.
Hint Resolve unsigned_repr: mortar.

Theorem signed_repr:
  forall z, min_signed <= z <= max_signed -> signed (repr z) = z.
Proof.
  intros. unfold signed. case (zle 0 z); intro.
  replace (unsigned (repr z)) with z.
  rewrite zlt_true. auto. unfold max_signed in H. omega.
  symmetry. apply unsigned_repr.
  split. auto. apply Zle_trans with max_signed. tauto.
  compute; intro; discriminate.
  pose (z' := z + modulus).
  replace (repr z) with (repr z').
  replace (unsigned (repr z')) with z'.
  rewrite zlt_false. unfold z'. omega.
  unfold z'. unfold min_signed in H.
  change modulus with (half_modulus + half_modulus). omega.
  symmetry. apply unsigned_repr.
  unfold z', max_unsigned. unfold min_signed, max_signed in H.
  change modulus with (half_modulus + half_modulus).
  omega.
  apply eqm_samerepr. unfold z'; red. exists 1. omega.
Qed.

(** ** Addition properties *)
Theorem add_unsigned: forall x y, add x y = repr (unsigned x + unsigned y).
Proof.
  intros; reflexivity.
Qed.

Theorem add_signed:
  forall x y, add x y = repr (signed x + signed y).
Proof.
  intros. rewrite add_unsigned. apply eqm_samerepr.
  apply eqm_add; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

Theorem add_commut:
  forall x y, add x y = add y x.
Proof. intros; unfold add. decEq. omega. Qed.

Theorem add_zero:
  forall x, add x zero = x.
Proof.
  intros; unfold add, zero. change (unsigned (repr 0)) with 0.
  rewrite Zplus_0_r. apply repr_unsigned.
Qed.

Theorem add_assoc:
  forall x y z, add (add x y) z = add x (add y z).
Proof.
  intros; unfold add.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr.
  apply eqm_trans with ((x' + y') + z').
  auto with mortar.
  rewrite <- Zplus_assoc. auto with mortar.
Qed.

Theorem add_permut:
  forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros.
  rewrite (add_commut y z).
  rewrite <- add_assoc.
  apply add_commut.
Qed.

Theorem add_neg_zero:
  forall x, add x (neg x) = zero.
Proof.
  intros; unfold add, neg, zero. apply eqm_samerepr.
  replace 0 with (unsigned x + (- (unsigned x))).
  auto with mortar.
  omega.
Qed.

(** ** Negation properties *)

Theorem neg_repr:
  forall z, neg (repr z) = repr (-z).
Proof.
  intros; unfold neg. apply eqm_samerepr. auto with mortar.
Qed.

Theorem neg_zero:
  neg zero = zero.
Proof.
  unfold neg, zero. compute. apply mkint_eq. trivial.
Qed.

Theorem neg_add_distr:
  forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  intros; unfold neg, add. apply eqm_samerepr.
  apply eqm_trans with (- (unsigned x + unsigned y)).
  auto with mortar.
  replace (- (unsigned x + unsigned y))
    with  ((- unsigned x) + (- unsigned y)).
  auto with mortar. omega.
Qed.

(** ** Subtraction properties *)

Theorem sub_zero_l:
  forall x, sub x zero = x.
Proof.
  intros; unfold sub. change (unsigned zero) with 0.
  replace (unsigned x - 0) with (unsigned x). apply repr_unsigned.
  omega.
Qed.

Theorem sub_zero_r:
  forall x, sub zero x = neg x.
Proof.
  intros; unfold sub, neg. change (unsigned zero) with 0.
  replace (0 - unsigned x) with (- unsigned x). auto. omega.
Qed.

Theorem sub_add_opp:
  forall x y, sub x y = add x (neg y).
Proof.
  intros; unfold sub, add, neg.
  replace (unsigned x - unsigned y)
    with  (unsigned x + (- unsigned y)).
  apply eqm_samerepr. auto with mortar.
  omega.
Qed.

Theorem sub_idem:
  forall x,
    sub x x = zero.
Proof.
  intros; unfold sub. replace (unsigned x - unsigned x) with 0. trivial.
  omega.
Qed.

Theorem sub_add_l:
  forall x y z,
    sub (add x y) z = add (sub x z) y.
Proof.
  intros. repeat rewrite sub_add_opp.
  repeat rewrite add_assoc. decEq. apply add_commut.
Qed.

Theorem sub_add_r:
  forall x y z, sub x (add y z) = add (sub x z) (neg y).
Proof.
  intros. repeat rewrite sub_add_opp.
  rewrite neg_add_distr. rewrite add_permut. apply add_commut.
Qed.

Theorem sub_shifted:
  forall x y z,
    sub (add x z) (add y z) = sub x y.
Proof.
  intros. rewrite sub_add_opp. rewrite neg_add_distr.
  rewrite add_assoc.
  rewrite (add_commut (neg y) (neg z)).
  rewrite <- (add_assoc z). rewrite add_neg_zero.
  rewrite (add_commut zero). rewrite add_zero.
  symmetry. apply sub_add_opp.
Qed.

(** ** Properties of multiplication *)

Theorem mul_commut:
  forall x y, mul x y = mul y x.
Proof.
  intros; unfold mul. decEq. ring.
Qed.

Theorem mul_zero:
  forall x, mul x zero = zero.
Proof.
  intros; unfold mul. change (unsigned zero) with 0.
  unfold zero. decEq. ring.
Qed.

Theorem mul_one:
  forall x, mul x one = x.
Proof.
  intros; unfold mul. change (unsigned one) with 1.
  transitivity (repr (unsigned x)). decEq. ring.
  apply repr_unsigned.
Qed.

Theorem mul_assoc:
  forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  intros; unfold mul.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr. apply eqm_trans with ((x' * y') * z').
  auto with mortar.
  rewrite <- Zmult_assoc. auto with mortar.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  intros; unfold mul, add.
  apply eqm_samerepr.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_trans with ((x' + y') * z').
  auto with mortar.
  replace ((x' + y') * z') with (x' * z' + y' * z').
  auto with mortar.
  ring.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  intros. rewrite mul_commut. rewrite mul_add_distr_l.
  decEq; apply mul_commut.
Qed.

Theorem neg_mul_distr_l:
  forall x y, neg(mul x y) = mul (neg x) y.
Proof.
  intros. unfold mul, neg.
  set (x' := unsigned x).  set (y' := unsigned y).
  apply eqm_samerepr. apply eqm_trans with (- (x' * y')).
  auto with mortar.
  replace (- (x' * y')) with ((-x') * y') by ring.
  auto with mortar.
Qed.

Theorem neg_mul_distr_r:
   forall x y, neg(mul x y) = mul x (neg y).
Proof.
  intros. rewrite (mul_commut x y). rewrite (mul_commut x (neg y)).
  apply neg_mul_distr_l.
Qed.


(** ** Properties of binary decompositions *)

Lemma Z_shift_add_bin_decomp:
  forall x,
    Z_shift_add (fst (Z_bin_decomp x)) (snd (Z_bin_decomp x)) = x.
Proof.
  destruct x; simpl.
  auto.
  destruct p; reflexivity.
  destruct p; try reflexivity. simpl.
  assert (forall z, 2 * (z + 1) - 1 = 2 * z + 1). intro; omega.
  generalize (H (Zpos p)); simpl. congruence.
Qed.

Lemma Z_shift_add_inj:
  forall b1 x1 b2 x2,
    Z_shift_add b1 x1 = Z_shift_add b2 x2 -> b1 = b2 /\ x1 = x2.
Proof.
  intros until x2.
  unfold Z_shift_add.
  destruct b1; destruct b2; intros;
  ((split; [reflexivity|omega]) || omegaContradiction).
Qed.

Lemma Z_of_bits_exten:
  forall n f1 f2,
    (forall z, 0 <= z < Z_of_nat n -> f1 z = f2 z) ->
    Z_of_bits n f1 = Z_of_bits n f2.
Proof.
  induction n; intros.
  reflexivity.
  simpl. rewrite inj_S in H. decEq. apply H. omega.
  apply IHn. intros; apply H. omega.
Qed.

Opaque Zmult.


Lemma Z_of_bits_of_Z:
  forall x, eqm (Z_of_bits word_size (bits_of_Z word_size x)) x.
Proof.
  assert (forall n x, exists k,
    Z_of_bits n (bits_of_Z n x) = k * two_power_nat n + x).
  induction n; intros.
  rewrite two_power_nat_O. simpl. exists (-x). omega.
  rewrite two_power_nat_S. simpl.
  caseEq (Z_bin_decomp x). intros b y ZBD. simpl.
  replace (Z_of_bits n
      (fun i => if zeq (i + 1) 0
                then b
                else bits_of_Z n y (i + 1 - 1)))
     with (Z_of_bits n (bits_of_Z n y)).
  elim (IHn y). intros k1 EQ1. rewrite EQ1.
  rewrite <- (Z_shift_add_bin_decomp x).
  rewrite ZBD. simpl.
  exists k1.
  case b; unfold Z_shift_add; ring.
  apply Z_of_bits_exten. intros.
  rewrite zeq_false. decEq. omega. omega.
  intro. exact (H word_size x).
Qed.

Lemma bits_of_Z_zero:
  forall n x, bits_of_Z n 0 x = false.
Proof.
  induction n; simpl; intros.
  auto.
  case (zeq x 0); intro. auto. auto.
Qed.

Remark Z_bin_decomp_2xm1:
  forall x, Z_bin_decomp (2 * x - 1) = (true, x - 1).
Proof.
  intros. caseEq (Z_bin_decomp (2 * x - 1)). intros b y EQ.
  generalize (Z_shift_add_bin_decomp (2 * x - 1)).
  rewrite EQ; simpl.
  replace (2 * x - 1) with (Z_shift_add true (x - 1)).
  intro. elim (Z_shift_add_inj _ _ _ _ H); intros.
  congruence. unfold Z_shift_add. omega.
Qed.

Lemma bits_of_Z_mone:
  forall n x,
  0 <= x < Z_of_nat n ->
  bits_of_Z n (two_power_nat n - 1) x = true.
Proof.
  induction n; intros.
  simpl in H. omegaContradiction.
  unfold bits_of_Z; fold bits_of_Z.
  rewrite two_power_nat_S. rewrite Z_bin_decomp_2xm1.
  rewrite inj_S in H. case (zeq x 0); intro. auto.
  apply IHn. omega.
Qed.

Lemma Z_bin_decomp_shift_add:
  forall b x, Z_bin_decomp (Z_shift_add b x) = (b, x).
Proof.
  intros. caseEq (Z_bin_decomp (Z_shift_add b x)); intros b' x' EQ.
  generalize (Z_shift_add_bin_decomp (Z_shift_add b x)).
  rewrite EQ; simpl fst; simpl snd. intro.
  elim (Z_shift_add_inj _ _ _ _ H); intros.
  congruence.
Qed.


Lemma bits_of_Z_of_bits:
  forall n f i,
  0 <= i < Z_of_nat n ->
  bits_of_Z n (Z_of_bits n f) i = f i.
Proof.
  induction n; intros; simpl.
  simpl in H. omegaContradiction.
  rewrite Z_bin_decomp_shift_add.
  case (zeq i 0); intro.
  congruence.
  rewrite IHn. decEq. omega. rewrite inj_S in H. omega.
Qed.

Lemma Z_of_bits_range:
  forall f, 0 <= Z_of_bits word_size f < modulus.
Proof.
  unfold max_unsigned, modulus.
  generalize word_size. induction n; simpl; intros.
  rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. generalize (IHn (fun i => f (i + 1))).
  set (x := Z_of_bits n (fun i => f (i + 1))).
  intro. destruct (f 0); unfold Z_shift_add; omega.
Qed.


Hint Resolve Z_of_bits_range: ints.

Lemma Z_of_bits_range_2:
  forall f, 0 <= Z_of_bits word_size f <= max_unsigned.
Proof.
  intros. unfold max_unsigned.
  generalize (Z_of_bits_range f). omega.
Qed.
Hint Resolve Z_of_bits_range_2: ints.

Lemma bits_of_Z_below:
  forall n x i, i < 0 -> bits_of_Z n x i = false.
Proof.
  induction n; simpl; intros.
  reflexivity.
  destruct (Z_bin_decomp x). rewrite zeq_false. apply IHn.
  omega. omega.
Qed.

Lemma bits_of_Z_above:
  forall n x i, i >= Z_of_nat n -> bits_of_Z n x i = false.
Proof.
  induction n; intros; simpl.
  reflexivity.
  destruct (Z_bin_decomp x). rewrite zeq_false. apply IHn.
  rewrite inj_S in H. omega. rewrite inj_S in H. omega.
Qed.

Opaque Zmult.

Lemma Z_of_bits_excl:
  forall n f g h,
  (forall i, 0 <= i < Z_of_nat n -> f i && g i = false) ->
  (forall i, 0 <= i < Z_of_nat n -> f i || g i = h i) ->
  Z_of_bits n f + Z_of_bits n g = Z_of_bits n h.
Proof.
  induction n.
  intros; reflexivity.
  intros. simpl. rewrite inj_S in H. rewrite inj_S in H0.
  rewrite <- (IHn (fun i => f(i+1))
                  (fun i => g(i+1))
                  (fun i => h(i+1))).
  assert (0 <= 0 < Zsucc(Z_of_nat n)). omega.
  unfold Z_shift_add.
  rewrite <- H0; auto.
  set (F := Z_of_bits n (fun i => f(i + 1))).
  set (G := Z_of_bits n (fun i => g(i + 1))).
  caseEq (f 0); intros; caseEq (g 0); intros; simpl.
  generalize (H 0 H1).
  rewrite H2; rewrite H3.
  simpl.
  intros; discriminate.
  omega. omega. omega.
  intros; apply H. omega.
  intros; apply H0. omega.
Qed.

(** ** Properties of bitwise and, or, xor *)

Lemma bitwise_binop_commut:
  forall f,
    (forall a b, f a b = f b a) ->
    forall x y,
      bitwise_binop f x y = bitwise_binop f y x.
Proof.
  unfold bitwise_binop; intros.
  decEq. apply Z_of_bits_exten; intros. auto.
Qed.

Lemma bitwise_binop_assoc:
  forall f,
  (forall a b c, f a (f b c) = f (f a b) c) ->
  forall x y z,
  bitwise_binop f (bitwise_binop f x y) z =
  bitwise_binop f x (bitwise_binop f y z).
Proof.
  unfold bitwise_binop; intros.
  repeat rewrite unsigned_repr; auto with ints.
  decEq. apply Z_of_bits_exten; intros.
  repeat (rewrite bits_of_Z_of_bits; auto).
Qed.
Lemma bitwise_binop_idem:
  forall f,
  (forall a, f a a = a) ->
  forall x,
  bitwise_binop f x x = x.
Proof.
  unfold bitwise_binop; intros.
  transitivity (repr (Z_of_bits
    word_size (bits_of_Z word_size (unsigned x)))).
  decEq. apply Z_of_bits_exten; intros. auto.
  transitivity (repr (unsigned x)).
  apply eqm_samerepr.
  apply Z_of_bits_of_Z.
  apply repr_unsigned.
Qed.

Theorem and_commut: forall x y,
  and x y = and y x.
Proof
  (bitwise_binop_commut andb andb_comm).

Theorem and_assoc: forall x y z,
  and (and x y) z = and x (and y z).
Proof
  (bitwise_binop_assoc andb andb_assoc).

Theorem and_zero: forall x,
  and x zero = zero.
Proof.
  unfold and, bitwise_binop, zero; intros.
  transitivity (repr
    (Z_of_bits word_size (bits_of_Z word_size 0))).
  decEq. apply Z_of_bits_exten. intros.
  change (unsigned (repr 0)) with 0.
  rewrite bits_of_Z_zero. apply andb_b_false.
  auto with ints.
Qed.

Lemma mone_max_unsigned:
  mone = repr max_unsigned.
Proof.
  unfold mone. apply eqm_samerepr. exists (-1).
  unfold max_unsigned. omega.
Qed.

Theorem and_mone: forall x, and x mone = x.
Proof.
  unfold and, bitwise_binop; intros.
  rewrite mone_max_unsigned. unfold max_unsigned, modulus.
  transitivity (repr
    (Z_of_bits word_size (bits_of_Z word_size (unsigned x)))).
  decEq. apply Z_of_bits_exten. intros.
  rewrite unsigned_repr. rewrite bits_of_Z_mone.
  apply andb_b_true. omega. compute. intuition congruence.
  transitivity (repr (unsigned x)).
  apply eqm_samerepr. apply Z_of_bits_of_Z.
  apply repr_unsigned.
Qed.

Theorem and_idem: forall x, and x x = x.
Proof.
  assert (forall b, b && b = b).
    destruct b; reflexivity.
  exact (bitwise_binop_idem andb H).
Qed.

Theorem or_commut: forall x y,
  or x y = or y x.
Proof (bitwise_binop_commut orb orb_comm).

Theorem or_assoc: forall x y z,
  or (or x y) z = or x (or y z).
Proof (bitwise_binop_assoc orb orb_assoc).

Theorem or_zero: forall x, or x zero = x.
Proof.
  unfold or, bitwise_binop, zero; intros.
  transitivity (repr
    (Z_of_bits word_size (bits_of_Z word_size (unsigned x)))).
  decEq. apply Z_of_bits_exten. intros.
  change (unsigned (repr 0)) with 0.
  rewrite bits_of_Z_zero. apply orb_b_false.
  transitivity (repr (unsigned x)); auto with ints.
  apply eqm_samerepr. apply Z_of_bits_of_Z.
  apply repr_unsigned.
Qed.

(*
Theorem or_mone: forall x, or x mone = mone.
Proof.
  rewrite mone_max_unsigned.
  unfold or, bitwise_binop; intros.
  decEq.
  transitivity (Z_of_bits word_size (bits_of_Z word_size max_unsigned)).
  apply Z_of_bits_exten. intros.
  change (unsigned (repr max_unsigned)) with max_unsigned.
  unfold max_unsigned, modulus. rewrite bits_of_Z_mone; auto.
  apply orb_b_true.
  apply eqm_small_eq; auto with ints. compute; intuition congruence.
Qed.
*)

Theorem or_idem: forall x, or x x = x.
Proof.
  assert (forall b, b || b = b).
    destruct b; reflexivity.
  exact (bitwise_binop_idem orb H).
Qed.

Theorem and_or_distrib:
  forall x y z,
  and x (or y z) = or (and x y) (and x z).
Proof.
  intros; unfold and, or, bitwise_binop.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  apply demorgan1.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof (bitwise_binop_commut xorb xorb_comm).

Theorem xor_assoc: forall x y z,
  xor (xor x y) z = xor x (xor y z).
Proof.
  assert (forall a b c, xorb a (xorb b c) =
                        xorb (xorb a b) c).
  symmetry. apply xorb_assoc.
  exact (bitwise_binop_assoc xorb H).
Qed.

Theorem xor_zero: forall x, xor x zero = x.
Proof.
  unfold xor, bitwise_binop, zero; intros.
  transitivity (repr
    (Z_of_bits word_size (bits_of_Z word_size (unsigned x)))).
  decEq. apply Z_of_bits_exten. intros.
  change (unsigned (repr 0)) with 0.
  rewrite bits_of_Z_zero. apply xorb_false.
  transitivity (repr (unsigned x)); auto with ints.
  apply eqm_samerepr. apply Z_of_bits_of_Z.
  apply repr_unsigned.
Qed.

Theorem xor_zero_one: xor zero one = one.
Proof. reflexivity. Qed.

Theorem xor_one_one: xor one one = zero.
Proof. reflexivity. Qed.

Theorem and_xor_distrib:
  forall x y z,
  and x (xor y z) = xor (and x y) (and x z).
Proof.
  intros; unfold and, xor, bitwise_binop.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  assert (forall a b c, a && (xorb b c) =
                        xorb (a && b) (a && c)).
    destruct a; destruct b; destruct c; reflexivity.
  auto.
Qed.

(** ** Properties necessary for JANUS *)

Theorem xor_x_x_zero:
  forall x,
    xor x x = zero.
Proof.
  unfold xor, bitwise_binop, zero; intros.
  transitivity (repr
    (Z_of_bits word_size (bits_of_Z word_size 0))).
  decEq. apply Z_of_bits_exten. intros.
  rewrite bits_of_Z_zero. apply xorb_nilpotent.
  auto with mortar.
Qed.

Lemma add_eq_r:
    forall x y z,
      add x y = add x z -> y = z.
Proof.
  intros.
  assert ((sub (add x y) x) = (sub (add x z) x)).
  unfold sub, add. grind.
  repeat rewrite sub_add_l in H0.
  repeat rewrite sub_idem in H0.
  rewrite add_commut in H0. rewrite add_zero in H0.
  rewrite add_commut in H0. rewrite add_zero in H0.
  assumption.
Qed.

Lemma add_neg_zero_r:
  forall x, add (neg x) x = zero.
Proof.
  intros. rewrite add_commut. apply add_neg_zero.
Qed.

Lemma sub_eq_l:
  forall x y z,
    sub x z = sub y z -> x = y.
Proof.
  intros.
  assert ((add (sub x z) z) = (add (sub y z) z)).
  grind.
  repeat rewrite sub_add_opp in H0.
  repeat rewrite add_assoc in H0.
  rewrite add_commut in H0.
  repeat rewrite add_neg_zero_r in H0.
  rewrite add_commut in H0.
  rewrite add_zero in H0.
  rewrite add_zero in H0.
  trivial.
Qed.

Lemma xor_mine:
  forall x y z,
    xor x y = xor x z -> y = z.
Proof.
  intros.
  assert (xor (xor x y) x = xor (xor x z) x).
  rewrite H. trivial.
  rewrite xor_commut in H0.
  rewrite <- xor_assoc in H0.
  rewrite xor_x_x_zero in H0.
  rewrite xor_commut in H0.
  rewrite xor_zero in H0.
  rewrite <- xor_commut in H0.
  rewrite <- xor_assoc in H0.
  rewrite xor_x_x_zero in H0.
  rewrite xor_commut in H0.
  rewrite xor_zero in H0.
  trivial.
Qed.

End Word32.