Require Import Eqdep.
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

Ltac decEq :=
  match goal with
    | [ |- _ = _ ] => f_equal
    | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

(* Chain injection and substition *)
Ltac inject H :=
  injection H; clear H; intros; try subst.

(* apply f to hypotheses *)
Ltac appHyps f :=
  match goal with
    | [ H : _ |- _] => f H
  end.

(* Try to find an element in [ls] that [f] likes *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(* Guard that x is in ls *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(* Hypothesis simplifier *)
Ltac simplHyp invOne :=
  let invert H F :=
    inList F invOne; (inversion H; fail)
    || (inversion H; [idtac]; clear H; try subst) in
      match goal with
        | [ H : ex _ |- _ ] => destruct H
        | [ H : ?F ?X = ?F ?Y |- _ ] => injection H;
          match goal with
            | [ |- F X = F Y -> _ ] => fail 1
            | [ |- _ = _ -> _ ] => try clear H; intros; try subst
          end
        | [ H : ?F _ _ = ?F _ _ |- _ ] => injection H;
          match goal with
            | [ |- _ = _ -> _ = _ -> _ ] => try clear H; intros; try subst
          end
        | [ H : ?F _ |- _ ] => invert H F
        | [ H : ?F _ _ |- _ ] => invert H F
        | [ H : ?F _ _ _ |- _ ] => invert H F
        | [ H : ?F _ _ _ _ |- _ ] => invert H F
        | [ H : ?F _ _ _ _ _ |- _ ] => invert H F
        | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] =>
          generalize (inj_pair2 _ _ _ _ _ H); clear H
        | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H
        | [ H : Some _ = Some _ |- _ ] => injection H; clear H
      end.

Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H; auto; [idtac]
  end.

Ltac rewriterP := repeat (rewriteHyp; autorewrite with mortar in *).
Ltac rewriter  := autorewrite with mortar in *; rewriterP.

Hint Rewrite app_ass : mortar.

Definition done (T : Type) (x : T) := True.

Ltac inster e trace :=
  match type of e with
    | forall x : _, _ =>
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      match trace with
        | (_, _) =>
          match goal with
            | [ H : done (trace, _) |- _ ] => fail 1
            | _ =>
              let T := type of e in
                match type of T with
                  | Prop =>
                    generalize e; intro;
                      assert (done (trace, tt)); [constructor | idtac]
                end
          end
      end
  end.

Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Ltac grind' lemmas invOne :=
  let sintuition := simpl in *; intuition; try subst;
    repeat (simplHyp invOne; intuition; try subst); try congruence in
      let rewriter := autorewrite with mortar in *;
        repeat (match goal with
                  | [ H : _ |- _ ] => (rewrite H; [])
                    || (rewrite H; [ | solve [grind' lemmas invOne] ])
                      || (rewrite H; [ | solve [grind' lemmas invOne] |
                        solve [grind' lemmas invOne ] ])
                end; autorewrite with mortar in *)
        in (sintuition; rewriter;
          match lemmas with
            | false => idtac
            | _ => repeat ((app ltac:(fun L => inster L L) lemmas
              || appHyps ltac:(fun L => inster L L));
                repeat (simplHyp invOne; intuition)); un_done
          end; sintuition; rewriter; sintuition; try omega;
          try (elimtype False; omega)).

Ltac grind := grind' false fail.

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


(* Proofs about functions *)
Lemma equal_f : forall (A B : Set) (f g : A -> B) (x : A), f = g -> f x = g x.
Proof.
  grind.
Qed.

Lemma equal_f_2 : forall (A B C : Set) (f g : A -> B -> C)
  (x : A) (y : B),
  f = g -> f x y = g x y.
Proof.
  grind.
Qed.

Lemma equal_f_3 : forall (A B C D : Set) (f g : A -> B -> C -> D)
  (x : A) (y : B) (z : C),
  f = g -> f x y z = g x y z.
Proof.
  grind.
Qed.

Lemma Zdiv_small:
  forall x y, 0 <= x < y -> x / y = 0.
Proof.
  intros. assert (y > 0). omega.
  assert (forall a b,
    0 <= a < y ->
    0 <= y * b + a < y ->
    b = 0).
  intros.
  assert (b = 0 \/ b > 0 \/ (-b) > 0). omega.
  elim H3; intro. auto.
  elim H4; intro. auto.
  assert (y * b >= y * 1). apply Zmult_ge_compat_l. omega. omega.
  omegaContradiction.
  assert (y * (-b) >= y * 1). apply Zmult_ge_compat_l. omega. omega.
  rewrite <- Zopp_mult_distr_r in H6. omegaContradiction.
  apply H1 with (x mod y).
  apply Z_mod_lt. auto.
  rewrite <- Z_div_mod_eq. auto. auto.
Qed.

Lemma Zmod_small:
  forall x y, 0 <= x < y -> x mod y = x.
Proof.
  intros. assert (y > 0). omega.
  generalize (Z_div_mod_eq x y H0).
  rewrite (Zdiv_small x y H). omega.
Qed.

Lemma Zmod_unique:
  forall x y a b,
    x = a * y + b -> 0 <= b < y -> x mod y = b.
Proof.
  intros. subst x. rewrite Zplus_comm.
  rewrite Z_mod_plus. apply Zmod_small. trivial. omega.
Qed.

Lemma Zdiv_unique:
  forall x y a b,
    x = a * y + b -> 0 <= b < y -> x / y = a.
Proof.
  intros. subst x. rewrite Zplus_comm.
  rewrite Z_div_plus. rewrite (Zdiv_small b y H0). omega. omega.
Qed.
