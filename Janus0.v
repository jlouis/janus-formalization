(* This file defines the Janus0 language which is a watered down version of JANUS,
 * containing only the most important parts of it
 *)

Require Import BaseLib.
Require Import ZArith.
Require Import Memory.
Require Import ZStore.

Module ZMem := Mem(ZS).

Section Janus0.

  Open Scope Z_scope.

  Definition Var := ZMem.var.
  Definition Value := ZMem.value.
  (* This section defines the expression language of Janus0 *)
  Section Expr.

    (* Minimal syntax definition *)
    Inductive Exp : Set :=
    | Exp_Const : Z -> Exp
    | Exp_Var : Var -> Exp
    | Exp_Add : Exp -> Exp -> Exp
    | Exp_Sub : Exp -> Exp -> Exp
    | Exp_Mul : Exp -> Exp -> Exp.

    Fixpoint denote_Exp (m : ZMem.memory) (e : Exp) {struct e} : option Z :=
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
            | (Some n1, Some n2) => Some (n1 - n2)
            | _ => None
          end
      end.

    Theorem exp_determ : forall m e v1 v2,
      denote_Exp m e = v1 -> denote_Exp m e = v2 -> v1 = v2.
    Proof.
      grind.
    Qed.

  End Expr.

  Section Stmt.
    Inductive Stm : Set :=
    | S_Incr : Var -> Exp -> Stm
    | S_Decr : Var -> Exp -> Stm
    | S_Semi : Stm -> Stm -> Stm
    | S_If : Exp -> Stm -> Stm -> Exp -> Stm.

    Definition mem := ZMem.memory.

    Inductive Stm_eval : mem -> Stm -> mem -> Prop :=
    | se_assvar_incr: forall (m m': mem) (v: Var) (z z' r: Z) (e: Exp),
      denote_Exp (ZMem.hide m v) e = Some z ->
      m v = Some z' ->
      r = (z + z') ->
      m' = ZMem.write m v r ->
      Stm_eval m (S_Incr v e) m'
    | se_assvar_decr: forall (m m': mem) (v: Var) (z z' r: Z) (e: Exp),
      denote_Exp (ZMem.hide m v) e = Some z ->
      m v = Some z' ->
      r = (z - z') ->
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

    Theorem fwd_det': forall (m m': mem) (s : Stm),
      Stm_eval m s m' -> (forall m'', Stm_eval m s m'' -> m' = m'').
    Proof.
      induction 1; intros.

      inversion H3. subst.
      assert (z' = z'0). assert (Some z' = Some z'0). rewrite <- H0. rewrite <- H7. trivial.
      injection H1. trivial.
      assert (z = z0). assert (Some z = Some z0). rewrite <- H. rewrite <- H6. trivial.
      injection H2. trivial. subst. trivial.

      inversion H3. subst.
      assert (z' = z'0). assert (Some z' = Some z'0). rewrite <- H0. rewrite <- H7. trivial.
      injection H1. trivial.
      assert (z = z0). assert (Some z = Some z0). rewrite <- H. rewrite <- H6. trivial.
      injection H2. trivial. subst. trivial.

      inversion H1. subst. apply IHStm_eval2. assert (m' = m'0). apply (IHStm_eval1 m'0). trivial.
      subst. trivial.

      inversion H4. subst. apply (IHStm_eval m''). trivial. congruence.
      inversion H4. subst. congruence. subst. apply (IHStm_eval m''). trivial.
    Qed.

    Theorem fwd_det : forall m m' m'' s,
      Stm_eval m s m' -> Stm_eval m s m'' -> m' = m''.
    Proof.
      intros. generalize m'' H0. eapply fwd_det'. eauto.
    Qed.

    Theorem bwd_det': forall m m' s,
      Stm_eval m' s m -> (forall m'', Stm_eval m'' s m -> m' = m'').
    Proof.
      induction 1; intros.

      inversion H3. subst.
      assert (ZMem.hide m v = ZMem.hide m'' v). eapply ZMem.write_hide. eauto.
      assert (z + z' = z0 + z'0). assert (ZMem.write m v (z + z') v = ZMem.write m'' v (z0 + z'0) v).
      apply equal_f. trivial. apply (ZMem.write_eq_2 m m'' v). trivial.
      assert (z = z0). assert (Some z = Some z0). grind. injection H4.
      trivial.
      subst.
      assert (z' = z'0). omega.
      subst. apply (ZMem.hide_eq m m'' v z'0). trivial. trivial. trivial.

      inversion H3. subst.
      assert (ZMem.hide m v = ZMem.hide m'' v). eapply ZMem.write_hide. eauto.
      assert (z - z' = z0 - z'0). assert (ZMem.write m v (z - z') v = ZMem.write m'' v (z0 - z'0) v).
      apply equal_f. trivial. apply (ZMem.write_eq_2 m m'' v). trivial.
      assert (z = z0). assert (Some z = Some z0). grind. injection H4.
      trivial.
      assert (z' = z'0). omega.
      subst. apply (ZMem.hide_eq m m'' v z'0). trivial. trivial. trivial.

      inversion H1. subst. assert (m' = m'0). apply IHStm_eval2. trivial.
      subst. apply IHStm_eval1. trivial.

      inversion H4. subst. apply IHStm_eval. trivial. congruence.
      inversion H4. subst. congruence. apply IHStm_eval. trivial.
    Qed.

    Theorem bwd_det: forall m m' m'' s,
      Stm_eval m' s m -> Stm_eval m'' s m -> m' = m''.
    Proof.
      intros. generalize m'' H0. apply bwd_det'. trivial.
    Qed.

  End Stmt.

End Janus0.