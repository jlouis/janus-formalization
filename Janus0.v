(* This file defines the Janus0 language which is a watered down version of JANUS,
 * containing only the most important parts of it
 *)

Require Import ZArith.
Require Import Memory.

Section Janus0.

  Open Scope Z_scope.
  (* This section defines the expression language of Janus0 *)
  Section Expr.

    Definition Var := nat.

    (* Minimal syntax definition *)
    Inductive Exp : Set :=
    | Exp_Const : Z -> Exp
    | Exp_Var : Var -> Exp
    | Exp_Add : Exp -> Exp -> Exp
    | Exp_Sub : Exp -> Exp -> Exp
    | Exp_Mul : Exp -> Exp -> Exp.

    Fixpoint denote_Exp (m : memory) (e : Exp) {struct e} : option Z :=
      match e with
        | E_Const z => Some z
        | E_Var x => m x
        | E_Add e1 e2 =>
            match (denoteExp e1, denoteExp e2) with
              | (Some n1, Some n2) => Some (n1 + n2)
              | _ => None
            end
        | E_Sub e1 e2 =>
          match (denoteExp e1, denoteExp e2) with
            | (Some n1, Some n2) => Some (n1 - n2)
            | _ => None
            end
        | E_Mul e1 e2 =>
          match (denoteExp e1, denoteExp e2) with
            | (Some n1, Some n2) => Some (n1 - n2)
            | _ => None
          end.



End Expr.

End Janus0.