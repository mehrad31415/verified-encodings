(* Parity.v — Parity (XOR) constraint definition
   Phase 2 (DRP Winter 2026)
   Based on src/parity/parity.lean by Codel, Avigad, Heule (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
Import ListNotations.

From VE Require Import cnf.Literal.
From VE Require Import cnf.Assignment.
From VE Require Import cnf.Clause.
From VE Require Import cnf.Cnf.
From VE Require Import cnf.Encoding.

Set Implicit Arguments.

(* Parity constraint: true iff an odd number of inputs are true *)
Definition parity : constraint := fun l => fold_right xorb false l.

(* ParityF: true iff an even number of inputs are true *)
Definition parityF : constraint := fun l => fold_right xorb true l.

Section ParityEval.

Variable V : Type.
Variable tau : assignment V.

Definition parity_eval (l : list (literal V)) : bool :=
  constraint_eval parity tau l.

Theorem parity_eval_nil : parity_eval [] = false.
Proof. reflexivity. Qed.

Theorem parity_eval_singleton : forall (lit : literal V),
  parity_eval [lit] = eval tau lit.
Proof.
  intro lit. unfold parity_eval, constraint_eval, parity. simpl.
  rewrite xorb_false_r. reflexivity.
Qed.

Theorem parity_eval_cons : forall (lit : literal V) (l : list (literal V)),
  parity_eval (lit :: l) = xorb (eval tau lit) (parity_eval l).
Proof.
  intros lit l. unfold parity_eval, constraint_eval, parity. simpl.
  reflexivity.
Qed.

End ParityEval.
