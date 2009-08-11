(* This file defines the Janus1 language which is a watered down
 * version of JANUS, only missing the loop construct.
 *)

Require Import Classical.
Require Import BaseLib.
Require Import Word32.
Require Import Memory.
Require Import W32Store.

Module W32Mem := Mem(W32S).

Section Janus1.

  Definition Var := W32Mem.var.
  Definition Value := W32Mem.value.

  (** * The Expression language *)

  Section Expr.

    (* Minimal syntax definition *)
    Inductive Exp : Set :=
    | Exp_Const : w32 -> Exp
    | Exp_Var : Var -> Exp

    (* Arithmetic *)
    | Exp_Add : Exp -> Exp -> Exp
    | Exp_Sub : Exp -> Exp -> Exp
    | Exp_Mul : Exp -> Exp -> Exp
    | Exp_Div : Exp -> Exp -> Exp
    | Exp_Mod : Exp -> Exp -> Exp

    (* Relational operators *)

    | Exp_Eq    : Exp -> Exp -> Exp
    | Exp_Neq   : Exp -> Exp -> Exp
    | Exp_And   : Exp -> Exp -> Exp
    | Exp_Or    : Exp -> Exp -> Exp
    | Exp_Lt    : Exp -> Exp -> Exp.

    Fixpoint denote_Exp (m : W32Mem.memory) (e : Exp) {struct e}
        : option w32 :=
      match e with
        | Exp_Const z => Some z
        | Exp_Var x => m x
        | Exp_Add e1 e2 =>
            match (denote_Exp m e1, denote_Exp m e2) with
              | (Some n1, Some n2) => Some (Word32.add n1 n2)
              | _ => None
            end
        | Exp_Sub e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n1, Some n2) => Some (Word32.sub n1 n2)
            | _ => None
            end
        | Exp_Mul e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n1, Some n2) => Some (Word32.mul n1 n2)
            | _ => None
          end
        | Exp_Div e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n1, Some n2) => Some (Word32.divu n1 n2)
            | _ => None
          end
        | Exp_Mod e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n1, Some n2) => Some (Word32.modu n1 n2)
            | _ => None
          end
        | Exp_Eq e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n1, Some n2) =>
                Some (if Word32.cmpu Ceq n1 n2
                      then Word32.one
                      else Word32.zero)
            | _ => None
          end
        | Exp_Neq e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n1, Some n2) =>
                Some (if Word32.cmpu Cne n1 n2
                      then Word32.one
                      else Word32.zero)
            | _ => None
          end
        | Exp_And e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n, Some n') =>
              match (Word32.unsigned n, Word32.unsigned n') with
                | (0, _) => Some Word32.zero
                | (_, 0) => Some Word32.zero
                | (_, _) => Some Word32.one
              end
            | _ => None
          end
        | Exp_Or e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n, Some n') =>
              match (Word32.unsigned n, Word32.unsigned n') with
                | (1, _) => Some Word32.one
                | (_, 1) => Some Word32.one
                | (_, _) => Some Word32.zero
              end
            | _ => None
          end
        | Exp_Lt e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n, Some n') =>
              Some (if Word32.cmpu Clt n n'
                    then Word32.one
                    else Word32.zero)
            | _ => None
          end
      end.

    Definition exp_equiv (e1: Exp) (e2: Exp) :=
      forall (v: Value) (m: W32Mem.memory),
        denote_Exp m e1 = Some v
        <->
        denote_Exp m e2 = Some v.

    (** ** Properties *)

    Lemma exp_equiv_refl: forall e, exp_equiv e e.
    Proof.
      unfold exp_equiv. grind.
    Qed.

    Lemma exp_equiv_sym: forall e1 e2,
      exp_equiv e1 e2 <-> exp_equiv e2 e1.
    Proof.
      unfold exp_equiv.
      intros. split. intros.
      symmetry.
      eapply H.
      intros.
      symmetry.
      eapply H.
    Qed.

    Lemma exp_equiv_tr: forall e1 e2 e3,
      exp_equiv e1 e2 -> exp_equiv e2 e3 -> exp_equiv e1 e3.
    Proof.
      unfold exp_equiv. intros.
      split.
      intro.
      assert (denote_Exp m e2 = Some v).
        eapply H. eauto.
        eapply H0. eauto.
      intro.
      assert (denote_Exp m e2 = Some v).
        eapply H0. eauto.
        eapply H. eauto.
    Qed.

    Theorem exp_determ : forall m e v1 v2,
      denote_Exp m e = v1
      -> denote_Exp m e = v2
      -> v1 = v2.
    Proof.
      grind.
    Qed.

  End Expr.

  (** * The Statement language *)

  Section Stmt.

    Inductive Stm : Set :=
    | S_Skip : Stm
    | S_Incr : Var -> Exp -> Stm
    | S_Decr : Var -> Exp -> Stm
    | S_Xor  : Var -> Exp -> Stm
    | S_Semi : Stm -> Stm -> Stm
    | S_If : Exp -> Stm -> Stm -> Exp -> Stm
    | S_Call : Z -> Stm
    | S_Uncall : Z -> Stm.

    Definition mem := W32Mem.memory.
    Definition defs := Z -> Stm.

    Inductive Stm_eval : defs -> mem -> Stm -> mem -> Prop :=
    | se_skip: forall d m, Stm_eval d m S_Skip m
    | se_assvar_incr: forall (d : defs) (m m': mem)
        (v: Var) (z z' r: w32) (e: Exp),
      denote_Exp (W32Mem.hide m v) e = Some z ->
      m v = Some z' ->
      r = (Word32.add z z') ->
      m' = W32Mem.write m v r ->
      Stm_eval d m (S_Incr v e) m'
    | se_assvar_decr: forall (d : defs) (m m': mem)
        (v: Var) (z z' r: w32) (e: Exp),
      denote_Exp (W32Mem.hide m v) e = Some z ->
      m v = Some z' ->
      r = (Word32.sub z' z) ->
      m' = W32Mem.write m v r ->
      Stm_eval d m (S_Decr v e) m'
    | se_assvar_xor: forall (d : defs) (m m': mem)
        (v: Var) (n n' n'': w32) (e: Exp),
      denote_Exp (W32Mem.hide m v) e = Some n ->
      m v = Some n' ->
      Word32.xor n n' = n'' ->
      m' = W32Mem.write m v n'' ->
      Stm_eval d m (S_Xor v e) m'
    | se_semi: forall (d : defs) (m m' m'': mem)
        (s1 s2: Stm),
      Stm_eval d m s1 m' ->
      Stm_eval d m' s2 m'' ->
      Stm_eval d m (S_Semi s1 s2) m''
    | se_if_t: forall (d : defs) (m m': mem)
        (e1 e2: Exp) (s1 s2: Stm) (k k': w32),
      denote_Exp m e1 = Some k ->
      Word32.is_true(k) ->
      Stm_eval d m s1 m' ->
      denote_Exp m' e2 = Some k' ->
      Word32.is_true(k') ->
      Stm_eval d m (S_If e1 s1 s2 e2) m'
    | se_if_f: forall (d : defs) (m m': mem)
        (e1 e2: Exp) (s1 s2: Stm) (k k': w32),
      denote_Exp m e1 = Some k ->
      Word32.is_false(k) ->
      Stm_eval d m s2 m' ->
      denote_Exp m' e2 = Some k' ->
      Word32.is_false(k') ->
      Stm_eval d m (S_If e1 s1 s2 e2) m'
    | se_call: forall (d : defs) (v : Z) (m m' : mem)
        (s : Stm),
      d v = s ->
      Stm_eval d m s m' ->
      Stm_eval d m (S_Call v) m'
    | se_uncall: forall (d : defs) (v : Z) (m m' : mem)
        (s : Stm),
      d v = s ->
      Stm_eval d m' s m ->
      Stm_eval d m (S_Uncall v) m'.

    Definition stm_equiv (s1 s2: Stm) :=
      forall (d : defs) (m m': W32Mem.memory),
        Stm_eval d m s1 m' <-> Stm_eval d m s2 m'.

    (** ** Properties *)

    (* Show stm_equiv *is* an equivalence relation *)
    Lemma stm_equiv_refl: forall s, stm_equiv s s.
    Proof.
      unfold stm_equiv. grind.
    Qed.

    Lemma stm_equiv_sym: forall s t, stm_equiv s t -> stm_equiv t s.
    Proof. unfold stm_equiv.
      intros. symmetry. apply H.
    Qed.

    Lemma stm_equiv_tr: forall s t u,
      stm_equiv s t -> stm_equiv t u -> stm_equiv s u.
    Proof.
      intros. unfold stm_equiv. intros. unfold stm_equiv in H.
      unfold stm_equiv in H0.
      grind. eapply H0. eauto. eapply H. eauto.
             eapply H. eauto. eapply H0. eauto.
    Qed.

    Lemma semi_assoc: forall s1 s2 s3,
      stm_equiv (S_Semi (S_Semi s1 s2) s3)
                (S_Semi s1 (S_Semi s2 s3)).
    Proof.
      intros. unfold stm_equiv. grind.
      inversion H. inversion H4. subst.
        assert (Stm_eval d m'1 (S_Semi s2 s3) m').
        constructor 5 with (m' := m'0);
          assumption.
        constructor 5 with (m' := m'1);
          assumption.
      inversion H. subst. inversion H6. subst.
        assert (Stm_eval d m (S_Semi s1 s2) m'1).
          constructor 5 with (m' := m'0);
            assumption.
        constructor 5 with (m' := m'1); assumption.
    Qed.

    Definition fwd_det G m s m' :=
      Stm_eval G m s m' ->
        forall m'', Stm_eval G m s m'' -> m' = m''.

    Definition bwd_det G m s m' :=
      Stm_eval G m s m' ->
        forall m'', Stm_eval G m'' s m' -> m = m''.

    Lemma b_forward_det: forall G m s m',
      (forall G m s m', bwd_det G m s m') -> fwd_det G m s m'.
    Proof.
      unfold fwd_det. intros until m'.
      intro. induction 1; intros.

      inversion H0. intuition.

      inversion H4. subst.
      assert (z' = z'0). grind.
      assert (z = z0). grind. grind.

      inversion H4. subst.
      assert (z' = z'0). grind.
      assert (z = z0). grind. grind.

      inversion H4. subst.
      assert (n = n0). grind.
      assert (n' = n'0). grind. grind.

      inversion H0. subst. apply IHStm_eval2.
      assert (m' = m'0).
        eapply IHStm_eval1. eauto.
      subst. trivial.

      inversion H5. subst.
      apply (IHStm_eval m'').
      trivial.
      congruence.
      inversion H5.
      subst.
      congruence.
      subst.
      apply (IHStm_eval m''). trivial.

      inversion H2. subst. apply IHStm_eval. trivial.
      inversion H2. subst. eapply H. eauto. trivial.
   Qed.

   Lemma b_backward_det: forall G m s m',
     (forall G m s m', fwd_det G m s m') -> bwd_det G m s m'.
   Proof.
      intros until m'. intro. unfold bwd_det. induction 1; intros.
      inversion H0. trivial.

      inversion H4. subst.
      assert (W32Mem.hide m v = W32Mem.hide m'' v).
        eapply W32Mem.write_hide. eauto.
      assert (Word32.add z z' = Word32.add z0 z'0).
      assert (W32Mem.write m v (Word32.add z z') v =
              W32Mem.write m'' v (Word32.add z0 z'0) v).
      apply equal_f. trivial.
      apply (W32Mem.write_eq_2 m m'' v). trivial.
      assert (z = z0).
      assert (Some z = Some z0).
        grind.
        grind.
      subst.
      assert (z' = z'0).
        eapply Word32.add_eq_r. eauto.
      subst.
      apply (W32Mem.hide_eq m m'' v z'0).
      trivial.
      trivial.
      trivial.

      inversion H4. subst.
      assert (W32Mem.hide m v = W32Mem.hide m'' v).
        eapply W32Mem.write_hide. eauto.
      assert (Word32.sub z' z = Word32.sub z'0 z0).
      assert (W32Mem.write m v (Word32.sub z' z) v =
              W32Mem.write m'' v (Word32.sub z'0 z0) v).
      apply equal_f. trivial.
      apply (W32Mem.write_eq_2 m m'' v). trivial.
      assert (z = z0).
      assert (Some z = Some z0); grind.
      assert (z' = z'0).
        subst. eapply Word32.sub_eq_l. eauto.
      subst. apply (W32Mem.hide_eq m m'' v z'0).
      trivial.
      trivial.
      trivial.

      inversion H4. subst.
      assert (W32Mem.hide m v = W32Mem.hide m'' v).
        eapply W32Mem.write_hide. eauto.
      assert (Word32.xor n n' = Word32.xor n0 n'0).
        assert (W32Mem.write m v (Word32.xor n n') v =
                W32Mem.write m'' v (Word32.xor n0 n'0) v).
      apply equal_f. trivial.
        eapply W32Mem.write_eq_2. eauto.
      assert (n = n0).
      assert (Some n = Some n0).
      rewrite H2 in H0. congruence. grind.
      subst.
      assert (n'0 = n').
        eapply Word32.xor_mine. eauto.
      subst.
        eapply (W32Mem.hide_eq m m'' v); eauto.

      inversion H0. subst.
      assert (m' = m'0). apply IHStm_eval2. trivial.
      subst. apply IHStm_eval1. trivial.

      inversion H5.
        subst. apply IHStm_eval. trivial. congruence.
      inversion H5.
        subst. congruence. apply IHStm_eval. trivial.

      inversion H2. subst. apply IHStm_eval. trivial.

      inversion H2. subst. eapply H. eauto. trivial.
    Qed.

    Theorem fwd_det_t: forall G m s m', fwd_det G m s m'
       with bwd_det_t: forall G m s m', bwd_det G m s m'.
    Proof.
    Admitted.

  End Stmt.

  (** * Statement inversion *)

  Section Invert.
    Fixpoint invert (s : Stm) {struct s} :=
      match s with
        | S_Skip => S_Skip
        | S_Incr x e => S_Decr x e
        | S_Decr x e => S_Incr x e
        | S_Xor x e => S_Xor x e
        | S_Semi s1 s2 => S_Semi (invert s2) (invert s1)
        | S_If e1 s1 s2 e2 => S_If e2 (invert s1) (invert s2) e1
        | S_Call d => S_Uncall d
        | S_Uncall d => S_Call d
      end.

    (** ** Properties *)

    Theorem invert_invert_id: forall s,
      invert (invert s) = s.
    Proof.
      induction s; grind.
    Qed.

    Theorem stm_inverter: forall G m s m',
      Stm_eval G m s m' <-> Stm_eval G m' (invert s) m.
    Proof.
      split. induction 1.
      simpl. constructor.
      inversion H. simpl.
      apply (se_assvar_decr d m' m v z r (Word32.sub r z)).
       rewrite H2. rewrite W32Mem.hide_write. assumption.
       rewrite H2. apply W32Mem.write_eq.
       trivial.
      apply (W32Mem.hide_eq m (W32Mem.write m' v (Word32.sub r z)) v z').
        assumption.
        assert (Word32.sub r z = z').
          rewrite H1.
          rewrite Word32.add_commut.
          rewrite Word32.sub_add_opp.
          rewrite Word32.add_assoc.
          rewrite Word32.add_neg_zero.
          rewrite Word32.add_zero.
          trivial.
        rewrite H3.
        apply W32Mem.write_eq.
        rewrite W32Mem.hide_write.
        rewrite H2.
        rewrite W32Mem.hide_write.
        trivial.
      simpl.
      apply (se_assvar_incr d m' m v z r (Word32.add r z)).
        rewrite H2.
        rewrite W32Mem.hide_write.
        assumption.
        rewrite H2.
        apply W32Mem.write_eq.
        rewrite Word32.add_commut.
        trivial.
      apply (W32Mem.hide_eq m (W32Mem.write m' v (Word32.add r z)) v z').
        trivial.
        rewrite W32Mem.write_eq.
        assert (Word32.add r z = z').
          rewrite H1.
          rewrite Word32.sub_add_opp.
          rewrite Word32.add_assoc.
          assert (Word32.add (Word32.neg z) z =
                  Word32.add z (Word32.neg z)).
            apply Word32.add_commut.
            rewrite H3.
            clear H3.
            rewrite Word32.add_neg_zero.
            rewrite Word32.add_zero.
            trivial.
            rewrite H3.
            trivial.
        rewrite W32Mem.hide_write.
        rewrite H2.
        rewrite W32Mem.hide_write.
        trivial.
      simpl. apply (se_assvar_xor d m' m v n n'' n').
        rewrite H2.
        rewrite W32Mem.hide_write.
        assumption.
        rewrite H2.
        apply W32Mem.write_eq.
        assert (n' = Word32.xor n n'').
        rewrite <- H1.
        rewrite <- Word32.xor_assoc.
        rewrite Word32.xor_x_x_zero.
        rewrite Word32.xor_commut.
        rewrite Word32.xor_zero.
        trivial.
        symmetry.
        trivial.
      apply (W32Mem.hide_eq m (W32Mem.write m' v n') v n').
        trivial.
        rewrite W32Mem.write_eq.
        trivial.
        rewrite W32Mem.hide_write.
        rewrite H2.
        rewrite W32Mem.hide_write.
        trivial.

      simpl. eapply se_semi. eauto. trivial.
      simpl. eapply se_if_t; eauto.
      simpl. eapply se_if_f; eauto.
      simpl. eapply se_uncall; eauto.
      simpl. eapply se_call; eauto.

      generalize m m'. induction s. intros. inversion H. constructor.
      intros.
      simpl in H. inversion H.
      apply (se_assvar_incr G m0 m'0 v z r (Word32.add r z)).
        rewrite H8.
        rewrite W32Mem.hide_write.
        assumption.
        rewrite H8.
        apply W32Mem.write_eq.
        rewrite Word32.add_commut.
        trivial.
      apply (W32Mem.hide_eq  m'0 (W32Mem.write m0 v (Word32.add r z)) v z').
        trivial.
        rewrite W32Mem.write_eq.
        rewrite H6.
        assert (z' = Word32.add (Word32.sub z' z) z).
          rewrite Word32.sub_add_opp.
          rewrite Word32.add_commut.
          rewrite Word32.add_permut.
          rewrite Word32.add_neg_zero.
          rewrite Word32.add_zero.
          trivial.
          rewrite <- H9.
          trivial.
          rewrite W32Mem.hide_write.
          rewrite H8.
          rewrite W32Mem.hide_write.
          trivial.
      intros.
      simpl in H. inversion H.
      apply (se_assvar_decr G m0 m'0 v z r (Word32.sub r z)).
        rewrite H8.
        rewrite W32Mem.hide_write.
        trivial.
        rewrite H8.
        apply W32Mem.write_eq.
        trivial.
        apply (W32Mem.hide_eq m'0
           (W32Mem.write m0 v (Word32.sub r z)) v z').
        trivial.
        assert (Word32.sub r z = z').
        rewrite H6.
        rewrite Word32.sub_add_opp.
        rewrite Word32.add_commut.
        rewrite <- Word32.add_assoc.
        assert (Word32.add (Word32.neg z) z =
                Word32.add z (Word32.neg z)).
        apply Word32.add_commut.
        rewrite H9.
        clear H9.
        rewrite Word32.add_neg_zero.
        rewrite Word32.add_commut.
        rewrite Word32.add_zero.
        trivial.
        rewrite H9.
        apply W32Mem.write_eq.
        rewrite W32Mem.hide_write.
        rewrite H8.
        rewrite W32Mem.hide_write.
        trivial.
      intros.
        simpl in H. inversion H.
      apply (se_assvar_xor G m0 m'0 v n n'' n').
        rewrite H8.
        rewrite W32Mem.hide_write. assumption.
        rewrite H8.
        apply W32Mem.write_eq.
        assert (n' = Word32.xor n n'').
        rewrite <- H6.
        rewrite <- Word32.xor_assoc.
        rewrite Word32.xor_x_x_zero.
        rewrite Word32.xor_commut.
        rewrite Word32.xor_zero.
        trivial.
        symmetry.
        trivial.
        apply (W32Mem.hide_eq m'0
          (W32Mem.write m0 v n') v n').
        trivial.
        apply W32Mem.write_eq.
        rewrite W32Mem.hide_write.
        rewrite H8.
        rewrite W32Mem.hide_write.
        trivial.
      intros.
      inversion H.
      apply (se_semi G m0 m'1 m'0).
      apply IHs1. trivial.
        apply IHs2. trivial.
      intros.
        inversion H. eapply se_if_t; eauto. eapply se_if_f; eauto.
      intros.
        inversion H. eapply se_call; eauto.
      intros.
        inversion H. eapply se_uncall; eauto.
    Qed.
  End Invert.
End Janus1.