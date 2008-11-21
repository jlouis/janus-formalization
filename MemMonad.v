Require Import Word32.
Require Import ZArith.

Set Implicit Arguments.

Definition var := nat.

(* A memory is a mapping from natural numbers to integers.
   The advantage of a "skew" is that we get it more precise that we are
   mapping variables into integers *)
Definition memory := var -> Z.
(* Set up that an empty cell maps to 0. This is the rule for JANUS *)
Definition empty (_ : Z) := 0.

(* Update the memory with a new value. We represent a memory as a function
   which will be extended with a new test whenever we write to the memory *)
Definition write (m : memory) a v x :=
  if eq_nat_dec a x
    then v
    else m x.

(** Set up a monad for memory as a heap transformer *)

(* Generalize the monad over return types >:-) *)
Definition memM (ret : Set) := memory -> memory * ret.

(* [Return T v] injects v into a T-type returner monad *)
Definition Return (T : Set) (v : T) : memM T :=
  fun m => (m, v).

(* Read a value from the memory. Reify it into the value-space *)
Definition Read a : memM Z :=
  fun m => (m, m a).

(* Write a value to memory. Write the value [v] to location [a] *)
Definition Write (a : var) (v : Z) : memM unit :=
  fun m => (write m a v, tt).

Definition Bind (T1 T2 : Set) (M1 : memM T1) (M2 : T1 -> memM T2) : memM T2 :=
  fun m =>
    let (m', v1) := M1 m in
      M2 v1 m'.

Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60).
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60).

(* Memory Specifications. Proofs about monadic values and specifications *)
Section mspec.

  (* T is any Set Type. P is a predicate on memory and T's *)
  Variables (T : Set) (P : memory -> T -> Prop).

  (* Define a memory specification on a monadic value to use the predicate
     on the monad in the obvious way *)
  Definition mspec (m1 : memM T) (m : memory) : Prop :=
    P (fst (m1 m)) (snd (m1 m)).

  Lemma mspec_Return : forall m v,
    P m v -> mspec (Return v) m.
  (* intros. unfold mspec. simpl. assumption. *)
    trivial.
  Qed.
End mspec.

(* Strengthening of mspec's. If we have mspec P1 holding and we have that P1 ==> P2, then we have
   mspec P2 holding *)
Section mspec_imp.
  Variable T : Set.
  Variables P1 P2 : memory -> T -> Prop.

  Variable m1 : memM T.
  Variable m : memory.

  Theorem mspec_imp : mspec P1 m1 m
    -> (forall m v, P1 m v -> P2 m v)
    -> mspec P2 m1 m.
   unfold mspec.
   (* intros. apply H0. assumption. *)
   intuition.
  Qed.
End mspec_imp.

Section mspec_Read.
  Variable P : memory -> Z -> Prop.

  Variable addr : var.
  Variable m : memory.

  Theorem mspec_Read :
    P m (m addr) -> mspec P (Read addr) m.
    trivial.
  Qed.
End mspec_Read.

Section mspec_Write.
  Variable P : memory -> unit -> Prop.

  Variable addr : var.
  Variable src : Z.
  Variable m : memory.

  Theorem mspec_Write :
    P (write m addr src) tt
    -> mspec P (Write addr src) m.
    trivial.
  Qed.
End mspec_Write.

Section mspec_Bind.
  Variables (T1 T2 : Set) (P : memory -> T2 -> Prop).

  Variable m1 : memM T1.
  Variable m2 : T1 -> memM T2.

  Theorem mspec_Bind : forall m,
    mspec (fun m v => mspec P (m2 v) m) m1 m
    -> mspec P (Bind m1 m2) m.
    unfold mspec, Bind; simpl; intro.
    destruct (m1 m); simpl.
    destruct (m2 t m0); trivial.
  Qed.
End mspec_Bind.

(* Proof automation hints *)
Lemma write_eq : forall m a v, write m a v a = v.
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

Ltac hyp_rewriter :=
  match goal with
   | [ H : context[write _ ?A _ ?A] |- _ ] =>
     rewrite write_eq in H
   | [ H : context[write _ ?A1 _ ?A2] |- _ ] =>
     rewrite write_ne in H; [idtac | omega]
  end.

Ltac monad_simplify :=
  match goal with
    | [ |- mspec _ (Return _) _]   => apply mspec_Return
    | [ |- mspec _ (Read _) _ ]    => apply mspec_Read
    | [ |- mspec _ (Write _ _) _ ] => apply mspec_Write
    | [ |- mspec _ (Bind _ _) _]   => apply mspec_Bind
    | [ |- mspec _ _ _ ] => eapply mspec_imp; [eauto; fail | idtac ]
  end.

Ltac memM_simplify := repeat progress (simplify; autorewrite with write;
  repeat hyp_rewriter; repeat monad_simplify).




