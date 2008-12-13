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

Require Import Arith.
Require Import Bool.
Require Import BaseLib.
Require Import Word32.
Require Import Memory.

Section Janus.
  (* Janus Expressions. These are taken from {PEPM2007}, Figure 1 *)
  (* TODO: Arrays *)
  Inductive Exp : Set :=
  | E_Const : w32 -> Exp
  | E_Var   : var -> Exp

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
     TODO: Arrays *)

  (* Function id's are just natural numbers *)
  Definition fid := nat.

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
  | S_Semi : Stmt -> Stmt -> Stmt

  (* Funcalls *)
  | S_Call : fid -> Stmt
  | S_Uncall : fid -> Stmt.

  (* Function environments maps fid's to Statements *)
  Definition fenv := fid -> Stmt.

  (* The empty function environment just gets replaced with a 'skip' construction.
     This is suboptimal, but we can change it to an optional type later *)
  Definition fenv_empty (_: var) := S_Skip.

  Definition def_func (G: fenv) fid stmts x :=
    if eq_nat_dec fid x
      then stmts
      else G x.

  (* What does an expression denote? Dynamic semantics of evaluating
     expressions in JANUS *)

  (* TODO: Arrays, Fractional product, Arrays *)
  Fixpoint denoteExp (m : memory) (e : Exp) {struct e} : option w32 :=
    match e with
      (* Arith *)
      | E_Const z => Some z
      | E_Var l => m l
      | E_Plus e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.add n n')
          | _ => None
        end
      | E_Minus e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.sub n n')
          | _ => None
        end
      | E_Mul e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.mul n n')
          | _ => None
        end
      | E_Div e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.divu n n')
          | _ => None
        end
      | E_Mod e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.modu n n')
          | _ => None
        end
      | E_FracProd e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.fracprodu n n')
          | _ => None
        end
      (* Bitwise *)
      | E_Bit_And e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.and n n')
          | _ => None
        end
      | E_Bit_Xor e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.xor n n')
          | _ => None
        end
      | E_Bit_Or e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') => Some (Word32.or n n')
          | _ => None
        end
      (* Relational *)
      | E_Eq e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') =>
            Some (if Word32.cmpu Ceq n n' then Word32.one else Word32.zero)
          | _ => None
        end
      | E_Neq e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') =>
            Some (if Word32.cmpu Cne n n' then Word32.one else Word32.zero)
          | _ => None
        end
      | E_Lt e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') =>
            Some (if Word32.cmpu Clt n n' then Word32.one else Word32.zero)
          | _ => None
        end
      | E_Gt e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') =>
            Some (if Word32.cmpu Cgt n n' then Word32.one else Word32.zero)
          | _ => None
        end
      | E_Leq e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') =>
            Some (if Word32.cmpu Cleq n n' then Word32.one else Word32.zero)
          | _ => None
        end
      | E_Geq e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') =>
            Some (if Word32.cmpu Cgeq n n' then Word32.one else Word32.zero)
          | _ => None
        end
      | E_And e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') =>
            match (Word32.unsigned n, Word32.unsigned n') with
              | (0, _) => Some Word32.zero
              | (_, 0) => Some Word32.zero
              | (_, _) => Some Word32.one
            end
          | _ => None
        end
      | E_Or e1 e2 =>
        match (denoteExp m e1, denoteExp m e2) with
          | (Some n, Some n') =>
            match (Word32.unsigned n, Word32.unsigned n') with
              | (1, _) => Some Word32.one
              | (_, 1) => Some Word32.one
              | (_, _) => Some Word32.zero
            end
          | _ => None
        end
    end.

  Theorem Exp_fwd_det : forall (m : memory) (e : Exp) v1 v2,
    (denoteExp m e = v1) /\ (denoteExp m e = v2) -> (v1 = v2).

  Qed.

  (** Operational semantics for Janus *)
  Inductive Stmt_loop_eval : fenv -> memory ->
      Exp -> Stmt -> Stmt -> Exp ->
      memory -> Prop :=
  | se_l_f: forall G m m' m'' m''' e1 s1 e2 s2 v1 v2,
      denoteExp m e2 = Some v2 ->
      Word32.is_false(v2) ->
      Stmt_eval G m s2 m' ->
      denoteExp m' e1 = Some v1 ->
      Word32.is_false(v1) ->
      Stmt_eval G m' s1 m'' ->
      Stmt_loop_eval G m'' e1 s1 s2 e2 m''' ->
      Stmt_loop_eval G m e1 s1 s2 e2 m'''
  | se_l_t: forall G m e1 s1 s2 e2 v2,
      denoteExp m e2 = Some v2 ->
      Word32.is_true(v2) ->
      Stmt_loop_eval G m e1 s1 s2 e2 m
  with Stmt_eval : fenv -> memory -> Stmt -> memory -> Prop :=
  | se_skip: forall G m,
      Stmt_eval G m S_Skip m
  | se_assvar_incr: forall G m v e n n' n'' m',
      denoteExp (hide m v) e = Some n ->
      m v = Some n'' ->
      Word32.add n n'' = n' ->
      write m v n' = m' ->
      Stmt_eval G m (S_Incr v e) m'
  | se_assvar_decr: forall G m v e n n' n'' m',
      denoteExp (hide m v) e = Some n ->
      m v = Some n'' ->
      Word32.add n n'' = n' ->
      write m v n' = m' ->
      Stmt_eval G m (S_Decr v e) m'
  | se_assvar_xor: forall G m v e n n' n'' m',
      denoteExp (hide m v) e = Some n ->
      m v = Some n'' ->
      Word32.add n n'' = n' ->
      write m v n' = m' ->
      Stmt_eval G m (S_Xor v e) m'
  | se_swap: forall G m v1 v2 n1 n2 m',
      m v1 = Some n1 ->
      m v2 = Some n2 ->
      (write (write m v1 n2) v2 n1) = m' ->
        Stmt_eval G m (S_Swap v1 v2) m'
  | se_semi: forall G s1 s2 m m' m'',
     Stmt_eval G m s1 m' ->
     Stmt_eval G m' s2 m'' ->
       Stmt_eval G m (S_Semi s1 s2) m'
  | se_if_true: forall G e1 e2 s1 s2 m m' n1 n2,
      denoteExp m e1 = Some n1 ->
      Word32.is_true(n1) ->
      Stmt_eval G m s1 m' ->
      denoteExp m' e2 = Some n2 ->
      Word32.is_true(n2) ->
        Stmt_eval G m (S_If e1 s1 s2 e2) m'
  | se_if_false: forall G e1 e2 s1 s2 m m' n1 n2,
      denoteExp m e1 = Some n1 ->
      Word32.is_false(n1) ->
      Stmt_eval G m s2 m' ->
      denoteExp m' e2 = Some n2 ->
      Word32.is_false(n2) ->
      Stmt_eval G m (S_If e1 s1 s2 e2) m'
  | se_loop_t: forall G m e1 s1 s2 e2 m' n1 n2,
      denoteExp m e1 = Some n1 ->
      Word32.is_true(n1) ->
      Stmt_eval G m s1 m' ->
      denoteExp m' e2 = Some n2 ->
      Word32.is_true(n2) ->
      Stmt_eval G m (S_Loop e1 s1 s2 e2) m'
  | se_loop: forall G e1 s1 s2 e2 m m' m'' n1 n2,
      denoteExp m e1 = Some n1 ->
      Word32.is_true(n1) ->
      Stmt_eval G m s1 m' ->
      denoteExp m' e2 = Some n2 ->
      Word32.is_false(n2) ->
      Stmt_loop_eval G m' e1 s1 s2 e2 m'' ->
      Stmt_eval G m (S_Loop e1 s1 s2 e2) m''
  | se_call: forall G m v m',
      Stmt_eval G m (G v) m' ->
      Stmt_eval G m (S_Call v) m'
  | se_uncall: forall G m v m',
      Stmt_eval G m' (G v) m ->
      Stmt_eval G m (S_Uncall v) m'.

  (* Produce a rather daunting induction principle on statements mutually
     inductive with the loop rules. *)
  Scheme stmt_eval_ind_2 := Induction for Stmt_eval Sort Prop
  with   loop_eval_ind_2 := Induction for Stmt_loop_eval Sort Prop.

  Fixpoint Stmt_invert (s: Stmt) : Stmt :=
    match s with
      | S_Incr v e => S_Decr v e
      | S_Decr v e => S_Incr v e
      | S_Xor v1 e => S_Xor v1 e
      | S_Swap v1 v2 => S_Swap v1 v2
      | S_If e1 s1 s2 e2 => S_If e2 (Stmt_invert s1) (Stmt_invert s2) e1
      | S_Loop e1 s1 s2 e2 => S_Loop e2 (Stmt_invert s1) (Stmt_invert s2) e1
      | S_Skip => S_Skip
      | S_Semi s1 s2 => S_Semi (Stmt_invert s2) (Stmt_invert s1)
      | S_Call v => S_Uncall v
      | S_Uncall v => S_Call v
    end.

  Theorem invert_self_inverse : forall (s: Stmt),
    Stmt_invert (Stmt_invert s) = s.

  Qed.

  Inductive fwd_det : fenv -> memory -> Stmt -> memory -> Prop :=
    | stmt_fwd:
      (forall G m s m',
           bwd_det G m s m') ->
           forall G m s m',
           fwd_det G m s m'

  with bwd_det : fenv -> memory -> Stmt -> memory -> Prop :=
    | stmt_bwd:
      (forall G m s m',
        fwd_det G m s m') ->
        forall G m s m',
        bwd_det G m s m'.

  Scheme fwd_det_ind_2 := Induction for fwd_det Sort Prop
  with   bwd_det_ind_2 := Induction for bwd_det Sort Prop.

  Lemma fwd_determinism': forall G m s m',
    fwd_det G m s m' ->
      Stmt_eval G m s m' -> forall m'', Stmt_eval G m s m'' -> m' = m''.
  Proof.
    apply (fwd_det_ind_2
      (fun G m s m' =>
        fun fd => Stmt_eval G m s m' -> forall m'', Stmt_eval G m s m'' -> m' = m'')
      (fun G m s m' =>
        fun fd => Stmt_eval G m s m' -> forall m'', Stmt_eval G m'' s m' -> m = m'')).
    intros bwd X.
    apply (stmt_eval_ind_2
    (fun (G: fenv) (m: memory) (s: Stmt) (m': memory) =>
      fun se => forall m'', Stmt_eval G m s m'' -> m' = m'')
    (fun (G: fenv) (m: memory) (e1: Exp) (s1 s2: Stmt) (e2: Exp) (m': memory)
      (le: Stmt_loop_eval G m e1 s1 s2 e2 m') =>
      forall m'',
        Stmt_loop_eval G m e1 s1 s2 e2 m'' -> m' = m'')); intros; try (inversion H; grind).

    inversion H1; grind. inversion H0; grind. inversion H0; grind.
    inversion H0; grind.
    inversion H0. apply H. assumption. assert (m' = m'0). apply H. assumption. grind.
    inversion H1. subst. assert (m' = m''0). apply H. assumption. grind.
      subst. assert (m' = m'0). apply H. assumption. subst. grind.
    inversion H0; grind.
    inversion H0. eapply X. eauto. assumption.
    inversion H2. assert (m' = m'0). apply H. assumption. subst.
      assert (m'' = m''1). apply H0. intuition. subst. apply H1. assumption. congruence.

    intros fwd X.
    apply (stmt_eval_ind_2
      (fun G m s m' (se: Stmt_eval G m s m') =>
        forall m'', Stmt_eval G m'' s m' -> m = m'')
      (fun G m e1 s1 s2 e2 m' le =>
        forall m'', Stmt_loop_eval G m'' e1 s1 s2 e2 m' -> m = m''));
    intros; try (inversion H; grind).

    Abort.


(*
  (* This only works for no UNCALL *)
  Lemma Stmt_eval_det : forall G m s m',
    Stmt_eval G m s m' -> forall m'',
      Stmt_eval G m s m'' -> m' = m''.
  Proof.
    apply
      (stmt_eval_ind_2
        stmt_det
        (fun G m e1 s1 s2 e2 m' =>
          fun le => forall m'',
            Stmt_loop_eval G m e1 s1 s2 e2 m'' -> m' = m''));
      unfold stmt_det; intros; try (inversion H; intuition); intros.

    inversion H1; intuition.
    inversion H0; [intuition | congruence].
    inversion H0; [congruence | intuition].
    inversion H0. intuition.
    assert (m' = m'0). intuition. subst. congruence.
    inversion H1. assert (m' = m''0). intuition. subst. congruence.
    assert (m' = m'0). intuition. apply H0. subst. trivial.

    inversion H0. intuition.
    inversion H2. apply H1. assert (m'' = m''1). apply H0.
      assert (m' = m'0); intuition; subst; trivial. subst. trivial.
  Qed.
*)
  (* Is a statement valid?
     This is just as simple congruence relation on statements *)
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