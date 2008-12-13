(* Janus Memories formalized *)

Require Import Arith.
Require Import BaseLib.
Require Import Word32.

Section Memory.
  (* Variables are natural numbers *)
  Definition var := nat.
  (* Memories are maps from variables to w32 optional types *)
  Definition memory := var -> option w32.
  (* The default store fails any lookup *)
  Definition empty (_ : var) : option w32 := None.

  (* Write [v] to memory location [x] in memory [m] *)
  Definition write (m : memory) x v x' :=
    if eq_nat_dec x x'
      then Some v
      else m x'.

  Definition hide (m : memory) x x' :=
    if eq_nat_dec x x'
      then None
      else m x'.

  (* Proof automation hints *)
  Lemma write_eq : forall m a v, write m a v a = Some v.
    unfold write.
    intros.
    destruct (eq_nat_dec a a); tauto.
  Qed.

  Hint Rewrite write_eq : mortar.

  Lemma write_eq_2 : forall m m' a v1 v2,
    write m a v1 a = write m' a v2 a -> v1 = v2.
  Proof.
    intros. assert (Some v1 = Some v2).
    assert (write m a v1 a = Some v1). apply write_eq.
    assert (write m' a v2 a = Some v2). apply write_eq.
    grind. injection H0. grind.
  Qed.


  Lemma write_ne : forall m a v a', a <> a'
    -> write m a v a' = m a'.
    unfold write.
    intros.
    destruct (eq_nat_dec a a'); tauto.
  Qed.

  Hint Rewrite write_ne using omega : mortar.

  Lemma hide_write : forall m m' x x' v1 v2 ,
    m = m' ->
      hide (write m x v1) x x' = hide (write m' x v2) x x'.
  Proof.
    intros. unfold hide, write. destruct (eq_nat_dec x x'); grind.
  Qed.

  Lemma hide_retract : forall m m' x,
    m = m' -> hide m x = hide m' x.
  Proof.
    intros. apply extensionality. intro. unfold hide.
    destruct (eq_nat_dec x x0); grind.
  Qed.

  Lemma write_extend : forall m m' x v,
    m = m' -> write m x v = write m' x v.
  Proof.
    grind.
  Qed.

  Lemma hide_irrel : forall m m' x,
    hide m x = hide m' x -> forall a, a <> x -> m a = m' a.
  Proof.
    intros. assert (hide m x a = hide m' x a).
    apply (f_ext nat (option w32) (hide m x) (hide m' x)). assumption.
    assert (hide m x a = m a). unfold hide. destruct (eq_nat_dec x a).
    symmetry in e. contradiction. trivial.
    assert (hide m' x a = m' a). unfold hide. destruct (eq_nat_dec x a).
    symmetry in e. contradiction. trivial.
    grind.
  Qed.

  Lemma write_neutral : forall m x v,
    m x = Some v -> write m x v = m.
  Proof.
    intros. apply extensionality. intro. unfold write.
    destruct (eq_nat_dec x x0); grind.
  Qed.

  Lemma hide_eq : forall m m' x v,
    m x = Some v -> m' x = Some v -> hide m x = hide m' x -> m = m'.
  Proof.
    intros.
    assert (forall a, a <> x -> m a = m' a). apply hide_irrel. assumption.
    assert (m = write m x v). symmetry. apply write_neutral; grind.
    assert (m' = write m' x v). symmetry. apply write_neutral; grind.
    rewrite H3. rewrite H4. apply extensionality. intro. unfold write.
    destruct (eq_nat_dec x x0). trivial. apply H2. apply sym_not_eq.
      assumption.
  Qed.

End Memory.
