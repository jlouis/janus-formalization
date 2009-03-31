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

End Janus0.