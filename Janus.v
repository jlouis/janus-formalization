(* Formalisation of the JANUS language itself
   The Operational semantics is taken from

   Glueck & Yokoyama - A Reversible Programming Language
     and its Invertible Self-Interpreter, PEPM 2007, Nice,France,
     ACM (cited as {PEPM2007})

*)

(* Current implementation is highly partial *)

(**
   TODO: List of no particular order
   ; Janus computation may fail. Adapt code.
   ; Prove that any program is invertible with the right result.
   ; Implement function definitions and function calls/uncalls.
*)

Require Import Word32.
Require Import Bool.
Require Import MemMonad.

Section Janus.
  (* Janus Expressions. These are taken from {PEPM2007}, Figure 1 *)
  (* TODO: Arrays *)
  Inductive Exp : Set :=
  | E_Const : w32 -> Exp
  | E_Var   : nat -> Exp

  (* Arithmetic *)
  | E_Plus  : Exp -> Exp -> Exp
  | E_Minus : Exp -> Exp -> Exp
  | E_Mul   : Exp -> Exp -> Exp
  | E_Div   : Exp -> Exp -> Exp
  | E_Mod   : Exp -> Exp -> Exp
  | E_FracProd : Exp -> Exp -> Exp

  (* Bitwise operations *)
  | E_Bit_Xor : Exp -> Exp -> Exp
  | E_Bit_And : Exp -> Exp -> Exp
  | E_Bit_Or : Exp -> Exp -> Exp

  (* Relational *)
  | E_Eq    : Exp -> Exp -> Exp
  | E_Neq   : Exp -> Exp -> Exp
  | E_And   : Exp -> Exp -> Exp
  | E_Or    : Exp -> Exp -> Exp
  | E_Lt    : Exp -> Exp -> Exp
  | E_Gt    : Exp -> Exp -> Exp
  | E_Leq   : Exp -> Exp -> Exp
  | E_Geq   : Exp -> Exp -> Exp.

  (* Statements in the JANUS language.
     TODO: Arrays, Funcalls *)
  Inductive Stmt : Set :=
  (* Skewed operations *)
  | S_Incr : var -> Exp -> Stmt
  | S_Decr : var -> Exp -> Stmt
  | S_Xor  : var -> Exp -> Stmt

  (* Misc *)
  | S_Swap : var -> var -> Stmt
  | S_Skip : Stmt

  (* Control flow *)
  | S_If : Exp -> Stmt -> Stmt -> Exp -> Stmt
  | S_Loop : Exp -> Stmt -> Stmt -> Exp -> Stmt

  (* Catenation *)
  | S_Semi : Stmt -> Stmt -> Stmt.

  (* What does an expression denote? Dynamic semantics of evaluating
     expressions in JANUS *)

  (* TODO: Arrays, Fractional product, Arrays *)
  Fixpoint denoteExp (m : memory) (e : Exp) {struct e} : w32 :=
    match e with
      (* Arithmetic *)
      | E_Const z => z
      | E_Var l => m l
      | E_Plus e1 e2 => Word32.add (denoteExp m e1) (denoteExp m e2)
      | E_Minus e1 e2 => Word32.sub (denoteExp m e1) (denoteExp m e2)
      | E_Mul e1 e2 => Word32.mul (denoteExp m e1) (denoteExp m e2)
      | E_Div e1 e2 => Word32.divu (denoteExp m e1) (denoteExp m e2)
      | E_Mod e1 e2 => Word32.modu (denoteExp m e1) (denoteExp m e2)
      | E_FracProd e1 e2 => Word32.fracprodu (denoteExp m e1) (denoteExp m e2)

      (* Bitwise *)
      | E_Bit_And e1 e2 => Word32.and (denoteExp m e1) (denoteExp m e2)
      | E_Bit_Xor e1 e2 => Word32.xor (denoteExp m e1) (denoteExp m e2)
      | E_Bit_Or  e1 e2 => Word32.or  (denoteExp m e1) (denoteExp m e2)

      (* Relational *)
      | E_Eq e1 e2 =>
        if Word32.cmpu Ceq (denoteExp m e1) (denoteExp m e2)
          then Word32.one
          else Word32.zero
      | E_Neq e1 e2 =>
        if Word32.cmpu Cne (denoteExp m e1) (denoteExp m e2)
          then Word32.one
          else Word32.zero
      | E_Lt e1 e2 =>
        if Word32.cmpu Clt (denoteExp m e1) (denoteExp m e2)
          then Word32.one
          else Word32.zero
      | E_Gt e1 e2 =>
        if Word32.cmpu Cgt (denoteExp m e1) (denoteExp m e2)
          then Word32.one
          else Word32.zero
      | E_Leq e1 e2 =>
        if Word32.cmpu Cleq (denoteExp m e1) (denoteExp m e2)
          then Word32.one
          else Word32.zero
      | E_Geq e1 e2 =>
        if Word32.cmpu Cgeq (denoteExp m e1) (denoteExp m e2)
          then Word32.one
          else Word32.zero
      | E_And e1 e2 =>
        match (Word32.unsigned (denoteExp m e1),
               Word32.unsigned (denoteExp m e2)) with
          | (0, _) => Word32.zero
          | (_, 0) => Word32.zero
          | (_, _) => Word32.one
        end
      | E_Or e1 e2 =>
        match (Word32.unsigned (denoteExp m e1),
               Word32.unsigned (denoteExp m e2)) with
          | (1, _) => Word32.one
          | (_, 1) => Word32.one
          | (_, _) => Word32.zero
        end
    end.

  Theorem Exp_fwd_det : forall (m : memory) (e : Exp) v1 v2,
    (denoteExp m e = v1) /\ (denoteExp m e = v2) -> (v1 = v2).
    intros m e v1 v2 [Eq1 Eq2]; congruence.
  Qed.

  (** Operational semantics for Janus *)
  (* Convenience function *)
  Definition Stmt_assvar m v e op :=
    (write m v (op (m v) (denoteExp m e))).

  Inductive Stmt_loop1_eval : memory -> Stmt -> memory -> Prop :=
  | se_l1_base: forall m m' e1 s1 s2 e2,
      Stmt_eval m s1 m' ->
        Stmt_loop1_eval m (S_Loop e1 s1 s2 e2) m'
  | se_l1_rec: forall m m' m'' m''' e1 s1 s2 e2,
      Stmt_eval m s1 m' ->
      Word32.is_false(denoteExp m' e2) ->
      Stmt_loop2_eval m' (S_Loop e1 s1 s2 e2) m'' ->
      Word32.is_false(denoteExp m'' e1) ->
      Stmt_eval m'' s1 m''' ->
        Stmt_loop1_eval m (S_Loop e1 s1 s2 e2) m'''
  with Stmt_loop2_eval : memory -> Stmt -> memory -> Prop :=
  | se_l2_base: forall m m' e1 s1 s2 e2,
      Stmt_eval m s2 m' ->
        Stmt_loop2_eval m (S_Loop e1 s1 s2 e2) m'
  | se_l2_rec: forall m m' m'' m''' e1 s1 s2 e2,
      Stmt_eval m s2 m' ->
      Word32.is_false(denoteExp m' e1) ->
      Stmt_loop1_eval m' (S_Loop e1 s1 s2 e2) m'' ->
      Word32.is_false(denoteExp m'' e2) ->
      Stmt_eval m'' s2 m''' ->
        Stmt_loop2_eval m (S_Loop e1 s1 s2 e2) m'''
  with Stmt_eval : memory -> Stmt -> memory -> Prop :=
  | se_skip: forall m,
      Stmt_eval m S_Skip m
  | se_assvar_incr: forall m v e,
      Stmt_eval m (S_Incr v e) (Stmt_assvar m v e Word32.add)
  | se_assvar_decr: forall m v e,
      Stmt_eval m (S_Decr v e) (Stmt_assvar m v e Word32.sub)
  | se_assvar_xor: forall m v e,
      Stmt_eval m (S_Xor v e) (Stmt_assvar m v e Word32.xor)
  | se_swap: forall (m: memory) (v1 v2: var),
      Stmt_eval m (S_Swap v1 v2)
        (let r1 := m v1 in
         let r2 := m v2 in
           (write (write m v1 r2) v2 r1))
  | se_semi: forall s1 s2 m m' m'',
     Stmt_eval m s1 m'' ->
     Stmt_eval m'' s2 m' ->
       Stmt_eval m (S_Semi s1 s2) m'
  | se_if_true: forall e1 e2 s1 s2 m m',
      Word32.is_true(denoteExp m e1) ->
      Stmt_eval m s1 m' ->
      Word32.is_true(denoteExp m' e2) ->
        Stmt_eval m (S_If e1 s1 s2 e2) m'
  | se_if_false: forall e1 e2 s1 s2 m m',
      Word32.is_false(denoteExp m e1) ->
      Stmt_eval m s2 m' ->
      Word32.is_false(denoteExp m' e2) ->
      Stmt_eval m (S_If e1 s1 s2 e2) m'
  | se_loop_main: forall m m' e1 s1 s2 e2,
      Word32.is_true(denoteExp m e1) ->
      Stmt_loop1_eval m (S_Loop e1 s1 s2 e2) m' ->
      Word32.is_true(denoteExp m' e2) ->
      Stmt_eval m (S_Loop e1 s1 s2 e2) m'.

  Fixpoint Stmt_invert (s: Stmt) : Stmt :=
    match s with
      | S_Incr v e => S_Decr v e
      | S_Decr v e => S_Incr v e
      | S_Xor v1 v2 => S_Xor v1 v2
      | S_Swap v1 v2 => S_Swap v1 v2
      | S_If e1 s1 s2 e2 => S_If e2 (Stmt_invert s1) (Stmt_invert s2) e1
      | S_Loop e1 s1 s2 e2 => S_Loop e2 (Stmt_invert s1) (Stmt_invert s2) e1
      | S_Skip => S_Skip
      | S_Semi s1 s2 => S_Semi (Stmt_invert s2) (Stmt_invert s1)
    end.

  Theorem invert_self_inverse : forall (s: Stmt),
    Stmt_invert (Stmt_invert s) = s.
    intros. induction s; simpl; intuition; congruence.
  Qed.

  (* TODO: Static semantics *)

  (* TODO: Where is Swap in {PEPM 2007}? *)

  (* TODO: Evaluation of statements *)

  (* TODO: Denotational semantics of the game *)

  (* TODO: Theorem 2, 3 *)

(*
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
*)
End Janus.