Require Export ZArith.
Require Export List.
Require Export Bool.

(* General tactics *)

(* Cut the goal into 2, solve the first with contradiction, the second with
   omega *)
Ltac omegaContradiction :=
  cut False; [contradiction|omega].

(* Definitions and theorems over the type [Z] *)

Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z_eq_dec.

Lemma zeq_true:
  forall (A: Set) (x: Z) (a b: A), (if zeq x x then a else b) = a.
  intros. case (zeq x x); intros.
  trivial. elim n. trivial.
Qed.

Lemma zeq_false: forall (A: Set) (x y: Z) (a b: A),
  x <> y -> (if zeq x y then a else b) = b.
  intros. case (zeq x y); intros.
  destruct H. assumption.
  reflexivity.
Qed.

Open Scope Z_scope.

Definition zlt: forall (x y: Z), {x < y} + {x >= y} := Z_lt_ge_dec.

Lemma zlt_true: forall (A: Set) (x y: Z) (a b: A),
  x < y -> (if zlt x y then a else b) = a.
  intros. case (zlt x y); intros.
  reflexivity.
  omegaContradiction.
Qed.

Lemma zlt_false: forall (A: Set) (x y: Z) (a b: A),
  x >= y -> (if zlt x y then a else b) = b.
  intros. case (zlt x y); intros.
  omegaContradiction.
  reflexivity.
Qed.

Definition zle: forall (x y: Z), {x <= y} + {x > y} := Z_le_gt_dec.

Lemma zle_true: forall (A: Set) (x y: Z) (a b: A),
  x <= y -> (if zle x y then a else b) = a.
  intros. case (zle x y); intros.
  reflexivity.
  omegaContradiction.
Qed.

Lemma zle_false: forall (A: Set) (x y: Z) (a b: A),
  x > y -> (if zle x y then a else b) = b.
  intros. case (zle x y); intros.
  omegaContradiction.
  reflexivity.
Qed.





