Require Export ZArith.
Require Export List.
Require Export Bool.

(* General Axioms *)

(* The first axiom (unprovable in Coq) is the one of extensionality.
   It is pretty simple. If forall x, f x = g x, then we have f = g.
*)
Axiom extensionality:
  forall (A B: Set) (f g: A -> B),
    (forall x, f x = g x) -> f = g.

(* The second axiom is that of proof irrelevance. If we have 2 ways
   to derive the same proposition, the way we derived it is irrelevant.
   This is rule is pretty basic in mathematics *)
Axiom proof_irrelevance:
  forall (P: Prop) (p1 p2: P), p1 = p2.

(* General tactics *)

(* Cut the goal into 2, solve the first with contradiction, the second with
   omega. The cut is modus ponens in inverse. *)
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

(* Properties about powers of 2 *)

Lemma two_power_nat_O : two_power_nat 0 = 1.
  reflexivity.
Qed.

Lemma two_power_nat_pos : forall (n : nat),
  two_power_nat n > 0.
  induction n. rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. omega.
Qed.



