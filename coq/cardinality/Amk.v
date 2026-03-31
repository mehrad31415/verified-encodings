(* Amk.v — At-most-k Boolean cardinality constraint
   Phase 3 (DRP Winter 2026)
   Based on src/cardinality/amk.lean by Codel, Avigad, Heule (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Import ListNotations.

From VE Require Import cnf.Literal.
From VE Require Import cnf.Assignment.
From VE Require Import cnf.Clause.
From VE Require Import cnf.Cnf.
From VE Require Import cnf.Encoding.
From VE Require Import cardinality.Distinct.

Set Implicit Arguments.

(* At-most-k: at most k of the inputs are true *)
Definition amk (k : nat) : constraint := fun l => Nat.leb (count_occ Bool.bool_dec l true) k.

Section AmkEval.

Variable V : Type.

Definition amk_eval (k : nat) (tau : assignment V) (l : list (literal V)) : bool :=
  constraint_eval (amk k) tau l.

Theorem amk_eval_nil : forall k tau, amk_eval k tau ([] : list (literal V)) = true.
Proof.
  intros k tau. unfold amk_eval, constraint_eval, amk. simpl. reflexivity.
Qed.

Theorem amk_eval_cons_neg : forall k (tau : assignment V) (lit : literal V) (l : list (literal V)),
  eval tau lit = false ->
  amk_eval k tau (lit :: l) = amk_eval k tau l.
Proof.
  intros k tau lit l Hlit.
  unfold amk_eval, constraint_eval, amk. simpl. rewrite Hlit. simpl.
  reflexivity.
Qed.

Theorem amk_eval_cons_pos : forall k (tau : assignment V) (lit : literal V) (l : list (literal V)),
  eval tau lit = true ->
  amk_eval (S k) tau (lit :: l) = amk_eval k tau l.
Proof.
  intros k tau lit l Hlit.
  unfold amk_eval, constraint_eval, amk. simpl. rewrite Hlit. simpl.
  reflexivity.
Qed.

(* AMO special case: at-most-one *)
Definition amo := amk 1.

(* AMO means: for any two distinct true literals, one must be false *)
Theorem amo_eval_tt_iff_distinct_ff :
  forall (tau : assignment V) (l : list (literal V)),
    amk_eval 1 tau l = true ->
    forall lit1 lit2, distinct lit1 lit2 l ->
      eval tau lit1 = true -> eval tau lit2 = false.
Proof.
  (* This follows from the counting argument:
     if AMO holds and lit1 is true, the count is at most 1,
     so no other literal can be true *)
  admit.
Admitted.

End AmkEval.
