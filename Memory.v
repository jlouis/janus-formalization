(** Janus Memories formalized *)

Require Import Arith.
Require Import BaseLib.

(** * The STORE signature *)

Module Type STORE.

  Parameter location : Set. (* Domain of the store mapping *)
  Parameter value : Set.    (* Codomain of the store mappring *)

  (* locations have equality *)
  Parameter eq : location -> location -> Prop.
  Parameter location_eq_dec : forall (n m : location),
    {n = m} + {n <> m}.

End STORE.

(** * The Mem functor *)

Module Mem(V : STORE).

  Definition var := V.location.
  Definition value := V.value. (* For convenience *)
  Definition memory := var -> option V.value.
  (* The default store fails any lookup *)
  Definition empty (_ : var) : option value := None.

  (* Write [v] to memory location [x] in memory [m] *)

  Definition write (m : memory) x v x' :=
    if V.location_eq_dec x x'
      then Some v
      else m x'.

  Definition hide (m : memory) x x' :=
    if V.location_eq_dec x x'
      then None
      else m x'.

  (* ** Properties *)

  Lemma write_eq : forall m a v, write m a v a = Some v.
    unfold write.
    intros.
    destruct (V.location_eq_dec a a); tauto.
  Qed.

  Hint Rewrite write_eq : mortar.

  Lemma write_eq_2 : forall m m' a v1 v2,
    write m a v1 a = write m' a v2 a -> v1 = v2.
  Proof.
    intros. assert (Some v1 = Some v2).
    assert (write m a v1 a = Some v1).
    apply write_eq.
    assert (write m' a v2 a = Some v2).
    apply write_eq.
    grind. injection H0. grind.
  Qed.


  Lemma write_ne : forall m a v a', a <> a'
    -> write m a v a' = m a'.
    unfold write.
    intros.
    destruct (V.location_eq_dec a a'); tauto.
  Qed.

  Hint Rewrite write_ne using omega : mortar.

  Lemma hide_write: forall m x v,
    hide (write m x v) x = hide m x.
  Proof.
    intros.
    apply extensionality. intro.
    unfold hide, write.
    destruct (V.location_eq_dec x x0).
    trivial.
    trivial.
  Qed.

  Lemma hide_write_2 : forall m m' x x' v1 v2 ,
    m = m' ->
      hide (write m x v1) x x' = hide (write m' x v2) x x'.
  Proof.
    intros.
    unfold hide, write.
    destruct (V.location_eq_dec x x'); grind.
  Qed.

  Lemma hide_retract : forall m m' x,
    m = m' -> hide m x = hide m' x.
  Proof.
    intros.
    apply extensionality. intro.
    unfold hide.
    destruct (V.location_eq_dec x x0); grind.
  Qed.

  Hint Rewrite hide_retract : mortar.

  Lemma write_extend : forall m m' x v,
    m = m' -> write m x v = write m' x v.
  Proof.
    grind.
  Qed.
  Hint Rewrite write_extend: mortar.

  Lemma hide_ne: forall m x x',
    x <> x' -> hide m x x' = m x'.
  Proof.
    intros.
    unfold hide.
    destruct (V.location_eq_dec x x').
    absurd (x = x'); assumption.
    trivial.
  Qed.

  Lemma hide_irrel : forall m m' x,
    hide m x = hide m' x -> forall a, a <> x -> m a = m' a.
  Proof.
    intros.
    assert (hide m x a = hide m' x a).
      apply
        (equal_f V.location
          (option value) (hide m x) (hide m' x)).
      assumption.
    assert (hide m x a = m a).
      unfold hide.
      destruct (V.location_eq_dec x a).
    symmetry in e. contradiction. trivial.
    assert (hide m' x a = m' a).
      unfold hide.
      destruct (V.location_eq_dec x a).
      symmetry in e. contradiction. trivial.
    grind.
  Qed.
  Hint Rewrite hide_irrel: mortar.

  Lemma write_neutral : forall m x v,
    m x = Some v -> write m x v = m.
  Proof.
    intros.
    apply extensionality.
    intro.
    unfold write.
    destruct (V.location_eq_dec x x0); grind.
  Qed.

  Hint Rewrite write_neutral : mortar.

  Lemma hide_eq : forall m m' x v,
    m x = Some v -> m' x = Some v -> hide m x = hide m' x -> m = m'.
  Proof.
    intros.
    assert (forall a, a <> x -> m a = m' a).
      apply hide_irrel.
      assumption.
    assert (m = write m x v).
      symmetry.
      apply write_neutral; grind.
    assert (m' = write m' x v).
      symmetry.
      apply write_neutral; grind.
    rewrite H3.
    rewrite H4.
    apply extensionality.
    intro.
    unfold write.
    destruct (V.location_eq_dec x x0).
    trivial.
    apply H2.
    apply sym_not_eq.
    assumption.
  Qed.
  Hint Rewrite hide_eq: mortar.

  Lemma write_hide : forall m m' x v1 v2,
    write m x v1 = write m' x v2 -> hide m x = hide m' x.
  Proof.
    intros.
    apply extensionality. intro.
    unfold hide.
    destruct (V.location_eq_dec x x0). trivial.
    assert ((write m x v1 x0) = m x0).
      apply write_ne.
      trivial.
    assert ((write m' x v2 x0) = m' x0).
      apply write_ne.
      trivial.
    grind.
  Qed.

End Mem.
