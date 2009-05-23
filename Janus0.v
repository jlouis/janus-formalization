(** This file defines the Janus0 language which is a watered down
    version of JANUS, containing only the most important parts of it *)

Require Import BaseLib.
Require Import ZArith.
Require Import Memory.
Require Import ZStore.

Module ZMem := Mem(ZS).

Section Janus0.

  Open Scope Z_scope.

  Definition Var := ZMem.var.
  Definition Value := ZMem.value.

  (** * The Expression language *)

  Section Expr.

    Inductive Exp : Set :=
    | Exp_Const : Z -> Exp
    | Exp_Var : Var -> Exp
    | Exp_Add : Exp -> Exp -> Exp
    | Exp_Sub : Exp -> Exp -> Exp
    | Exp_Mul : Exp -> Exp -> Exp.

    Fixpoint denote_Exp (m : ZMem.memory) (e : Exp) {struct e}
        : option Z :=
      match e with
        | Exp_Const z => Some z
        | Exp_Var x => m x
        | Exp_Add e1 e2 =>
            match (denote_Exp m e1, denote_Exp m e2) with
              | (Some n1, Some n2) => Some (n1 + n2)
              | _ => None
            end
        | Exp_Sub e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n1, Some n2) => Some (n1 - n2)
            | _ => None
            end
        | Exp_Mul e1 e2 =>
          match (denote_Exp m e1, denote_Exp m e2) with
            | (Some n1, Some n2) => Some (n1 * n2)
            | _ => None
          end
      end.

    Definition exp_equiv (e1: Exp) (e2: Exp) :=
      forall (v: Value) (m: ZMem.memory),
        denote_Exp m e1 = Some v <-> denote_Exp m e2 = Some v.

    (** ** Properties *)

    Lemma exp_equiv_refl: forall e,
      exp_equiv e e.
    Proof.
      unfold exp_equiv.
      grind.
    Qed.

    Lemma exp_equiv_sym: forall e1 e2,
      exp_equiv e1 e2 <-> exp_equiv e2 e1.
    Proof.
      unfold exp_equiv. intros.
      split.
        intros. symmetry. eapply H.
        intros. symmetry. eapply H.
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
      denote_Exp m e = v1 -> denote_Exp m e = v2 -> v1 = v2.
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
    | S_Semi : Stm -> Stm -> Stm
    | S_If : Exp -> Stm -> Stm -> Exp -> Stm.

    Definition mem := ZMem.memory.

    Inductive Stm_eval : mem -> Stm -> mem -> Prop :=
    | se_skip: forall m, Stm_eval m S_Skip m
    | se_assvar_incr: forall (m m': mem) (v: Var) (z z' r: Z) (e: Exp),
      denote_Exp (ZMem.hide m v) e = Some z ->
      m v = Some z' ->
      r = (z + z') ->
      m' = ZMem.write m v r ->
      Stm_eval m (S_Incr v e) m'
    | se_assvar_decr: forall (m m': mem) (v: Var) (z z' r: Z) (e: Exp),
      denote_Exp (ZMem.hide m v) e = Some z ->
      m v = Some z' ->
      r = (z' - z) ->
      m' = ZMem.write m v r ->
      Stm_eval m (S_Decr v e) m'
    | se_semi: forall (m m' m'': mem) (s1 s2: Stm),
      Stm_eval m s1 m' ->
      Stm_eval m' s2 m'' ->
      Stm_eval m (S_Semi s1 s2) m''
    | se_if_t: forall (m m': mem) (e1 e2: Exp) (s1 s2: Stm) (k k': Z),
      denote_Exp m e1 = Some k ->
      k <> 0 ->
      Stm_eval m s1 m' ->
      denote_Exp m' e2 = Some k' ->
      k' <> 0 ->
      Stm_eval m (S_If e1 s1 s2 e2) m'
    | se_if_f: forall (m m': mem) (e1 e2: Exp) (s1 s2: Stm) (k k': Z),
      denote_Exp m e1 = Some k ->
      k = 0 ->
      Stm_eval m s2 m' ->
      denote_Exp m' e2 = Some k' ->
      k' = 0 ->
      Stm_eval m (S_If e1 s1 s2 e2) m'.

    Definition stm_equiv (s1 s2: Stm) :=
      forall (m m': ZMem.memory),
        Stm_eval m s1 m' <-> Stm_eval m s2 m'.

    (** ** Properties *)

    Lemma stm_equiv_refl: forall s, stm_equiv s s.
    Proof.
      unfold stm_equiv. grind.
    Qed.

    Lemma stm_equiv_sym: forall s t, stm_equiv s t -> stm_equiv t s.
    Proof.
      unfold stm_equiv.
      intros.
      symmetry.
      apply H.
    Qed.

    Lemma stm_equiv_tr: forall s t u,
      stm_equiv s t -> stm_equiv t u -> stm_equiv s u.
    Proof.
      intros. unfold stm_equiv.
      intros. unfold stm_equiv in H.
      unfold stm_equiv in H0.
      grind.
      eapply H0. eauto.
      eapply H. eauto.
      eapply H. eauto.
      eapply H0. eauto.
    Qed.

    Lemma semi_assoc: forall s1 s2 s3,
      stm_equiv
        (S_Semi (S_Semi s1 s2) s3)
        (S_Semi s1 (S_Semi s2 s3)).
    Proof.
      intros.
      unfold stm_equiv. grind.
      inversion H.
      subst.
      inversion H3.
      subst.
      assert (Stm_eval m'1 (S_Semi s2 s3) m').
        constructor 4 with (m' := m'0);
          assumption.
        constructor 4 with (m' := m'1);
          assumption.
      inversion H.
      subst.
      inversion H5.
      subst.
        assert (Stm_eval m (S_Semi s1 s2) m'1).
          constructor 4 with (m' := m'0);
            assumption.
          constructor 4 with (m' := m'1);
            assumption.
    Qed.

    Theorem fwd_det': forall (m m': mem) (s : Stm),
      Stm_eval m s m' ->
        (forall m'', Stm_eval m s m'' -> m' = m'').
    Proof.
      induction 1; intros.
      inversion H. trivial.

      inversion H3. subst.
      assert (z' = z'0).
      assert (Some z' = Some z'0).
      rewrite <- H0.
      rewrite <- H7.
      trivial.
      injection H1.
      trivial.
      assert (z = z0).
      assert (Some z = Some z0).
      rewrite <- H.
      rewrite <- H6.
      trivial.
      injection H2.
      trivial.
      subst.
      trivial.

      inversion H3.
      subst.
      assert (z' = z'0).
      assert (Some z' = Some z'0).
      rewrite <- H0.
      rewrite <- H7.
      trivial.
      injection H1.
      trivial.
      assert (z = z0).
      assert (Some z = Some z0).
      rewrite <- H.
      rewrite <- H6.
      trivial.
      injection H2.
      trivial.
      subst.
      trivial.

      inversion H1.
      subst.
      apply IHStm_eval2.
      assert (m' = m'0).
        apply (IHStm_eval1 m'0). trivial.
      subst.
      trivial.

      inversion H4. subst.
      apply (IHStm_eval m''). trivial. congruence.
      inversion H4. subst.
      congruence. subst. apply (IHStm_eval m''). trivial.
    Qed.

    Theorem fwd_det : forall m m' m'' s,
      Stm_eval m s m' -> Stm_eval m s m'' -> m' = m''.
    Proof.
      intros. generalize m'' H0.
      eapply fwd_det'. eauto.
    Qed.

    Theorem bwd_det': forall m m' s,
      Stm_eval m' s m ->
        (forall m'', Stm_eval m'' s m -> m' = m'').
    Proof.
      induction 1; intros.
      inversion H. trivial.

      inversion H3. subst.
      assert (ZMem.hide m v = ZMem.hide m'' v).
        eapply ZMem.write_hide. eauto.
      assert (z + z' = z0 + z'0).
      assert (ZMem.write m v (z + z') v =
              ZMem.write m'' v (z0 + z'0) v).
      apply equal_f. trivial.
      apply (ZMem.write_eq_2 m m'' v). trivial.
      assert (z = z0).
      assert (Some z = Some z0).
      grind. injection H4.
      trivial.
      subst.
      assert (z' = z'0). omega.
      subst.
      apply (ZMem.hide_eq m m'' v z'0).
      trivial.
      trivial.
      trivial.

      inversion H3. subst.
      assert (ZMem.hide m v = ZMem.hide m'' v).
        eapply ZMem.write_hide. eauto.
      assert (z' - z = z'0 - z0).
      assert (ZMem.write m v (z' - z) v =
              ZMem.write m'' v (z'0 - z0) v).
      apply equal_f. trivial.
      apply (ZMem.write_eq_2 m m'' v). trivial.
      assert (z = z0).
      assert (Some z = Some z0).
        grind.
        injection H4.
      trivial.
      assert (z' = z'0). omega.
      subst.
      apply (ZMem.hide_eq m m'' v z'0).
      trivial.
      trivial.
      trivial.

      inversion H1. subst.
      assert (m' = m'0).
      apply IHStm_eval2.
      trivial.
      subst.
      apply IHStm_eval1.
      trivial.

      inversion H4.
      subst. apply IHStm_eval. trivial. congruence.
      inversion H4.
      subst. congruence. apply IHStm_eval. trivial.
    Qed.

    Theorem bwd_det: forall m m' m'' s,
      Stm_eval m' s m -> Stm_eval m'' s m -> m' = m''.
    Proof.
      intros. generalize m'' H0.
      apply bwd_det'. trivial.
    Qed.

  End Stmt.

  (** * Statement inversion *)

  Section Invert.
    Fixpoint invert (s : Stm) {struct s} :=
      match s with
        | S_Skip => S_Skip
        | S_Incr x e => S_Decr x e
        | S_Decr x e => S_Incr x e
        | S_Semi s1 s2 => S_Semi (invert s2) (invert s1)
        | S_If e1 s1 s2 e2 => S_If e2 (invert s1) (invert s2) e1
      end.

    (** ** Properties *)

    Theorem invert_invert_id: forall s,
      invert (invert s) = s.
    Proof.
      induction s; grind.
    Qed.

    Theorem stm_inverter: forall m m' s,
      Stm_eval m s m' <-> Stm_eval m' (invert s) m.
    Proof.
      split. induction 1.
      simpl. constructor.
      inversion H. simpl.
      apply (se_assvar_decr m' m v z r (r - z)).
       rewrite H2. rewrite ZMem.hide_write. assumption.
       rewrite H2. apply ZMem.write_eq.
       trivial.
      apply (ZMem.hide_eq m (ZMem.write m' v (r - z)) v z').
        assumption.
        assert (r - z = z'). omega. rewrite H3. apply ZMem.write_eq.
        rewrite ZMem.hide_write. rewrite H2. rewrite ZMem.hide_write.
        trivial.
      simpl.
      apply (se_assvar_incr m' m v z r (r + z)).
        rewrite H2. rewrite ZMem.hide_write. assumption.
        rewrite H2. apply ZMem.write_eq. omega.
      apply (ZMem.hide_eq m (ZMem.write m' v (r + z)) v z').
        trivial. rewrite ZMem.write_eq. assert (r + z = z'). omega.
        rewrite H3. trivial.
        rewrite ZMem.hide_write. rewrite H2. rewrite ZMem.hide_write.
        trivial.
      simpl. eapply se_semi. eauto. trivial.
      simpl. eapply se_if_t; eauto.
      simpl. eapply se_if_f; eauto.

      generalize m m'. induction s. intros. inversion H. constructor.
      intros.
      simpl in H. inversion H.
      apply (se_assvar_incr m0 m'0 v z r (r + z)).
        rewrite H7. rewrite ZMem.hide_write. assumption.
        rewrite H7. apply ZMem.write_eq. omega.
      apply (ZMem.hide_eq m'0 (ZMem.write m0 v (r + z)) v z').
        trivial.
        rewrite ZMem.write_eq.
        rewrite H5.
        assert (z' = z' - z + z). omega.
          rewrite <- H8. trivial.
          rewrite ZMem.hide_write.
          rewrite H7.
          rewrite ZMem.hide_write.
          trivial.
      intros.
      simpl in H. inversion H.
      apply (se_assvar_decr m0 m'0 v z r (r - z)).
        rewrite H7. rewrite ZMem.hide_write. trivial.
        rewrite H7. apply ZMem.write_eq. trivial.
        apply (ZMem.hide_eq m'0 (ZMem.write m0 v (r - z)) v z').
        trivial.
        assert (r - z = z'). rewrite H5. omega.
        rewrite H8. apply ZMem.write_eq.
        rewrite ZMem.hide_write. rewrite H7. rewrite ZMem.hide_write.
        trivial.
      intros.
      inversion H. apply (se_semi m0 m'1 m'0). apply IHs1. trivial.
        apply IHs2. trivial.
      intros.
        inversion H. eapply se_if_t; eauto. eapply se_if_f; eauto.
    Qed.
  End Invert.
End Janus0.
