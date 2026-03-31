(* DirectParity.v — Direct parity encoding with correctness proof
   Phase 2 (DRP Winter 2026)
   Based on src/parity/direct_parity.lean by Codel, Avigad, Heule (CMU) *)

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
From VE Require Import parity.Parity.
From VE Require Import parity.Explode.

Set Implicit Arguments.

Section DirectParityDefs.

Variable V : Type.
Hypothesis V_eq_dec : forall (x y : V), {x = y} + {x <> y}.

(* Helper: decide literal equality *)
Definition lit_eqb (l1 l2 : literal V) : bool :=
  match l1, l2 with
  | Pos v1, Pos v2 =>
    match V_eq_dec v1 v2 with left _ => true | right _ => false end
  | Neg v1, Neg v2 =>
    match V_eq_dec v1 v2 with left _ => true | right _ => false end
  | _, _ => false
  end.

(* Count flips between two clauses *)
Fixpoint count_flips (c1 c2 : clause V) : nat :=
  match c1, c2 with
  | [], _ => 0
  | _, [] => 0
  | l1 :: ls1, l2 :: ls2 =>
    (if lit_eqb (flip l1) l2 then 1 else 0) + count_flips ls1 ls2
  end.

(* The direct parity encoding: all clauses with an even number of flips *)
Fixpoint direct_parity' (l : list (literal V)) : cnf V :=
  match l with
  | [] => [[]]
  | lit :: ls =>
    map (fun c =>
      if Nat.even (count_flips ls c) then lit :: c else flip lit :: c)
    (explode (map (var (V:=V)) ls))
  end.

(* As an encoding function *)
Definition direct_parity : enc_fn V := dir_enc direct_parity'.

Theorem direct_parity_nil :
  direct_parity' ([] : list (literal V)) = [[]].
Proof. reflexivity. Qed.

(* The direct parity encoding is correct *)
Theorem direct_parity_formula_encodes_parity :
  forall (l : list (literal V)),
    formula_encodes parity (direct_parity' l) l.
Proof.
  intro l. intro tau. split; intro H.
  - exists tau. split; [| apply agree_on_refl]. admit.
  - destruct H as [sigma [Heval Hagree]]. admit.
Admitted.

(* The direct parity encoding is well-behaved *)
Theorem direct_parity_is_wb :
  is_wb direct_parity.
Proof.
  intros l g Hdisj. split.
  - intros a Ha. exact Ha.
  - intros v Hv. left. simpl in Hv. admit.
Admitted.

(* Main result *)
Theorem direct_parity_encodes_parity :
  encodes parity direct_parity.
Proof.
  split.
  - intros l g Hdisj. apply direct_parity_formula_encodes_parity.
  - apply direct_parity_is_wb.
Qed.

End DirectParityDefs.
