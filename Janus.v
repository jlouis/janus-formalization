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
    grind.
  Qed.

  (** Operational semantics for Janus *)
  Inductive Stmt_loop_eval : fenv -> memory ->
      Exp -> Stmt -> Stmt -> Exp ->
      memory -> Prop :=
  | se_l_t: forall G m e1 s1 s2 e2 v2,
      denoteExp m e2 = Some v2 ->
      Word32.is_true(v2) ->
      Stmt_loop_eval G m e1 s1 s2 e2 m
  | se_l_f: forall G m m' m'' m''' e1 s1 e2 s2 v1 v2,
      denoteExp m e2 = Some v2 ->
      Word32.is_false(v2) ->
      Stmt_eval G m s2 m' ->
      denoteExp m' e1 = Some v1 ->
      Word32.is_false(v1) ->
      Stmt_eval G m' s1 m'' ->
      Stmt_loop_eval G m'' e1 s1 s2 e2 m''' ->
      Stmt_loop_eval G m e1 s1 s2 e2 m'''
  with Stmt_eval : fenv -> memory -> Stmt -> memory -> Prop :=
  | se_call: forall G m v m',
      Stmt_eval G m (G v) m' ->
      Stmt_eval G m (S_Call v) m'
  | se_uncall: forall G m v m',
      Stmt_eval G m' (G v) m ->
      Stmt_eval G m (S_Uncall v) m'
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
      Word32.sub n'' n = n' ->
      write m v n' = m' ->
      Stmt_eval G m (S_Decr v e) m'
  | se_assvar_xor: forall G m v e n n' n'' m',
      denoteExp (hide m v) e = Some n ->
      m v = Some n'' ->
      Word32.xor n n'' = n' ->
      write m v n' = m' ->
      Stmt_eval G m (S_Xor v e) m'
(*  | se_swap: forall G m v1 v2 n1 n2 m',
      m v1 = Some n1 ->
      m v2 = Some n2 ->
      (write (write m v1 n2) v2 n1) = m' ->
        Stmt_eval G m (S_Swap v1 v2) m' *)
  | se_semi: forall G s1 s2 m m' m'',
     Stmt_eval G m s1 m' ->
     Stmt_eval G m' s2 m'' ->
       Stmt_eval G m (S_Semi s1 s2) m''
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
  | se_loop: forall G e1 s1 s2 e2 m m' m'' n1,
      denoteExp m e1 = Some n1 ->
      Word32.is_true(n1) ->
      Stmt_eval G m s1 m' ->
      Stmt_loop_eval G m' e1 s1 s2 e2 m'' ->
      Stmt_eval G m (S_Loop e1 s1 s2 e2) m''.

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
  Proof.
    induction s; grind.
  Qed.

  Lemma hide_write_neutral_no_ext: forall m v x a,
    hide (write m v x) v a = hide m v a.
  Proof.
    intros. unfold hide. destruct (eq_nat_dec v a).
    trivial.
    apply write_ne. trivial.
  Qed.

  Lemma hide_write_neutral: forall m v x,
    hide (write m v x) v = hide m v.
  Proof.
    intros; apply extensionality. apply hide_write_neutral_no_ext.
  Qed.

  Lemma hide_write_simpl: forall m v x a,
    hide (write m v x) v a = hide m v a.
  Proof.
    intros. unfold hide. destruct (eq_nat_dec v a). trivial.
    apply write_ne. trivial.
  Qed.

  Lemma hide_write_simpl_ext: forall m v x,
    hide (write m v x) v = hide m v.
  Proof.
    intros. apply extensionality. apply hide_write_simpl.
  Qed.

  Definition fwd_det G m s m' :=
    Stmt_eval G m s m' -> forall m'', Stmt_eval G m s m'' -> m' = m''.

  Definition bwd_det G m s m' :=
    Stmt_eval G m s m' -> forall m'', Stmt_eval G m'' s m' -> m = m''.

  Lemma b_forward_det: forall G m s m',
    (forall G m s m', bwd_det G m s m') -> fwd_det G m s m'.
  Proof.
    unfold fwd_det. intros until m'. intro. intro.
    apply (stmt_eval_ind_2
      (fun G m s m' (se : Stmt_eval G m s m') => forall m'',
        Stmt_eval G m s m'' -> m' = m'')
      (fun G m e1 s1 s2 e2 m' (sle : Stmt_loop_eval G m e1 s1 s2 e2 m') =>
        forall m'',
          Stmt_loop_eval G m e1 s1 s2 e2 m'' -> m' = m'')).
    intros. inversion H2; grind.
    intros. inversion H2; unfold bwd_det in H. eapply H. eauto.
    assumption.
    intros; inversion H1; grind.
    intros; inversion H1; grind.
    intros; inversion H1; grind.
    intros; inversion H1; grind.
    (* Semi *)
    intros. inversion H3. subst. apply H2. assert (m'0 = m'1). apply H1.
    trivial. subst. trivial.
    (* If *)
    intros; inversion H2; subst. apply H1. trivial. congruence.
    intros; inversion H2; subst. apply H1. congruence. apply H1. trivial.
    (* Loop *)
    intros. inversion H3; subst. apply H2. assert (m'0 = m'1). apply H1.
    trivial. subst. trivial.
    (* Loop-Base *)
    intros. inversion H1; grind.
    intros. inversion H4; subst.
      congruence. apply H3. assert (m''= m''1). apply H2.
        assert (m'0 = m'1). apply H1. trivial. subst. trivial. subst. trivial.
    trivial.
  Qed.

  Lemma f_backward_det: forall G m s m',
    (forall G m s m', fwd_det G m s m') -> bwd_det G m s m'.
  Proof.
    unfold bwd_det. intros until m'. intro. intro.
    apply (stmt_eval_ind_2
      (fun G m s m' (se : Stmt_eval G m s m') => forall m'',
        Stmt_eval G m'' s m' -> m = m'')
      (fun G m e1 s1 s2 e2 m' (sle : Stmt_loop_eval G m e1 s1 s2 e2 m') =>
        forall m'',
          Stmt_loop_eval G m'' e1 s1 s2 e2 m' -> m = m'')).
    intros. inversion H2; grind.
    intros. inversion H2. subst. unfold fwd_det in H. eapply H; eauto.
    intros. inversion H1; grind.
    intros. inversion H1; grind.
      (* TODO: Use Math rules to do this *)

    Abort.

End Janus.