(* Formalisation of the JANUS language itself *)

(* Current implementation is highly partial *)
Require Import Arith.
Require Import ZArith.
Require Import MemMonad.


Section Janus.
  Open Scope Z_scope.
  Inductive Exp : Set :=
  | E_Const : Z -> Exp
  | E_Var   : nat -> Exp
  | E_Plus  : Exp -> Exp -> Exp
  | E_Minus : Exp -> Exp -> Exp
  | E_Mul   : Exp -> Exp -> Exp.

  Fixpoint denoteExp (m : memory) (e : Exp) {struct e} : Z :=
    match e with
      | E_Const z => z
      | E_Var l => m l
      | E_Plus e1 e2 => denoteExp m e1 + denoteExp m e2
      | E_Minus e1 e2 => denoteExp m e1 - denoteExp m e2
      | E_Mul e1 e2 => denoteExp m e1 * denoteExp m e2
    end.
End Janus.