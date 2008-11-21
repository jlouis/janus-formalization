(* Formalisation of the JANUS language itself *)

(* Current implementation is highly partial *)

(**
   TODO: List of no particular order
   ; Janus computation may fail. Adapt code.
   ; Prove that any program is invertible with the right result.
   ; Implement function definitions and function calls/uncalls.
*)

Require Import ZArith.
Require Import Bool.
Require Import MemMonad.

Section Janus.
  Open Scope Z_scope.

  Inductive Exp : Set :=
  | E_Const : Z -> Exp
  | E_Var   : nat -> Exp
  | E_Plus  : Exp -> Exp -> Exp
  | E_Minus : Exp -> Exp -> Exp
  | E_Mul   : Exp -> Exp -> Exp
  | E_Eq    : Exp -> Exp -> Exp
  | E_Neq   : Exp -> Exp -> Exp
  | E_And   : Exp -> Exp -> Exp
  | E_Or    : Exp -> Exp -> Exp.

  Fixpoint denoteExp (m : memory) (e : Exp) {struct e} : Z :=
    match e with
      | E_Const z => z
      | E_Var l => m l
      | E_Plus e1 e2 => denoteExp m e1 + denoteExp m e2
      | E_Minus e1 e2 => denoteExp m e1 - denoteExp m e2
      | E_Mul e1 e2 => denoteExp m e1 * denoteExp m e2
      | E_Eq e1 e2 =>
        if Z_eq_dec (denoteExp m e1) (denoteExp m e2)
          then 1
          else 0
      | E_Neq e1 e2 =>
        if Z_eq_dec (denoteExp m e1) (denoteExp m e2)
          then 0
          else 1
      | E_And e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (0,_) => 0
          | (_,0) => 0
          | (_,_) => 1
        end
      | E_Or e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (1,_) => 1
          | (_,1) => 1
          | (_,_) => 0
        end
    end.

  Theorem Exp_fwd_det : forall (m : memory) (e : Exp) v1 v2,
    (denoteExp m e = v1) /\ (denoteExp m e = v2) -> (v1 = v2).
    induction e; intuition.
  Qed.

  Inductive Stmt : Set :=
  | S_Incr : var -> Exp -> Stmt
  | S_Decr : var -> Exp -> Stmt
  | S_Swap : var -> var -> Stmt
  | S_If : Exp -> Stmt -> Stmt -> Exp -> Stmt
  | S_Semi : Stmt -> Stmt -> Stmt.


  Fixpoint denoteStmt (s : Stmt) : memM unit :=
    match s with
      | S_Incr v e =>
        (fun m =>
          (r <- Return (denoteExp m e);
            r' <- Read v ;
            Write v (r + r')) m)
      | S_Decr v e =>
        (fun m =>
          (r <- Return (denoteExp m e);
            r' <- Read v ;
            Write v (r - r')) m)
      | S_Swap v1 v2 =>
        r1 <- Read v1 ;
        r2 <- Read v2 ;
        Write v1 r2 ;;
        Write v2 r1
      | S_Semi s1 s2 => (denoteStmt s1) ;; (denoteStmt s2)
      | S_If b t e a =>
        (fun m =>
          (* Wrong at the moment *)
          (match denoteExp m b with
             | 0 => denoteStmt e
             | _ => denoteStmt t
          end) m)
    end.

    Fixpoint invert (s : Stmt) : Stmt :=
      match s with
        | S_Incr v e => S_Decr v e
        | S_Decr v e => S_Incr v e
        | S_Swap v1 v2 => S_Swap v1 v2
        | S_If b t f a => S_If a (invert t) (invert f) b
        | S_Semi s1 s2 => S_Semi (invert s2) (invert s1)
      end.

    Theorem invert_self_inverse :
      forall s, invert (invert s) = s.
      induction s; intuition;
      simpl; rewrite IHs1; rewrite IHs2; reflexivity.
    Qed.
End Janus.