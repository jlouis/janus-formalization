(* Janus Memories formalized *)

Require Import Arith.
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

  Hint Rewrite write_eq : write.

  Lemma write_ne : forall m a v a', a <> a'
    -> write m a v a' = m a'.
    unfold write.
    intros.
    destruct (eq_nat_dec a a'); tauto.
  Qed.

  Hint Rewrite write_ne using omega : write.

  Lemma write_eq_2 : forall m m' a v v',
    write m a v a = write m' a v' a -> v = v'.
  Proof.
    unfold write. intros. destruct (eq_nat_dec a a). injection H. trivial.
    contradiction n. trivial.
  Qed.

  Lemma write_eq_3 : forall m m' a v v' x,
    write m a v x = write m' a v' x -> v = v' \/ m x = m' x.
    unfold write. intros. destruct (eq_nat_dec a x). injection H. auto.
    auto.
  Qed.

  (* Want to prove a number of propositions on stores/memories here
     to make it possible to do full backwards determinism. *)

End Memory.
