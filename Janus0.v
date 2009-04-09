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

  End Stmt.

End Janus0.