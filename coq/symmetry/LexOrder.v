(* LexOrder.v — Lexicographic ordering on boolean lists
   Extension: Symmetry-breaking predicates for SAT encodings
   DRP Winter 2026, UWaterloo Women in Math
   Mentor: Mehrad Haghshenas *)

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

Set Implicit Arguments.

Section LexOrderDefs.

(* Lexicographic <= on boolean lists.
   false < true, so [false; true] < [true; false].
   Shorter lists are <= longer lists (prefix ordering). *)
Fixpoint lex_le (l1 l2 : list bool) : bool :=
  match l1, l2 with
  | [], _ => true
  | _ :: _, [] => false
  | false :: r1, true :: _ => true
  | true :: _, false :: _ => false
  | _ :: r1, _ :: r2 => lex_le r1 r2
  end.

(* Basic evaluation lemmas *)

Theorem lex_le_nil_l : forall l, lex_le [] l = true.
Proof. destruct l; reflexivity. Qed.

Theorem lex_le_nil_r : forall b l, lex_le (b :: l) [] = false.
Proof. intros b l. destruct b; reflexivity. Qed.

Theorem lex_le_cons : forall b1 b2 r1 r2,
  lex_le (b1 :: r1) (b2 :: r2) =
    ((negb b1 && b2) || (Bool.eqb b1 b2 && lex_le r1 r2))%bool.
Proof.
  intros [] [] r1 r2; simpl; try reflexivity.
Qed.

(* Reflexivity *)
Theorem lex_le_refl : forall l, lex_le l l = true.
Proof.
  induction l as [| b l' IH].
  - reflexivity.
  - destruct b; simpl; exact IH.
Qed.

(* Transitivity *)
Theorem lex_le_trans : forall l1 l2 l3,
  lex_le l1 l2 = true -> lex_le l2 l3 = true -> lex_le l1 l3 = true.
Proof.
  induction l1 as [| b1 r1 IH]; intros l2 l3 H12 H23.
  - reflexivity.
  - destruct l2 as [| b2 r2]; [destruct b1; discriminate |].
    destruct l3 as [| b3 r3]; [destruct b2; discriminate |].
    destruct b1, b2, b3; simpl in *; try discriminate; try reflexivity;
    try (eapply IH; eassumption).
Qed.

(* Antisymmetry for same-length lists *)
Theorem lex_le_antisym : forall l1 l2,
  length l1 = length l2 ->
  lex_le l1 l2 = true -> lex_le l2 l1 = true -> l1 = l2.
Proof.
  induction l1 as [| b1 r1 IH]; intros l2 Hlen H12 H21.
  - destruct l2; [reflexivity | simpl in Hlen; discriminate].
  - destruct l2 as [| b2 r2]; [simpl in Hlen; discriminate |].
    simpl in Hlen. injection Hlen as Hlen.
    destruct b1, b2; simpl in H12, H21; try discriminate.
    + f_equal. eapply IH; eassumption.
    + f_equal. eapply IH; eassumption.
Qed.

(* Totality for same-length lists *)
Theorem lex_le_total : forall l1 l2,
  length l1 = length l2 ->
  lex_le l1 l2 = true \/ lex_le l2 l1 = true.
Proof.
  induction l1 as [| b1 r1 IH]; intros l2 Hlen.
  - left. reflexivity.
  - destruct l2 as [| b2 r2]; [simpl in Hlen; discriminate |].
    simpl in Hlen. injection Hlen as Hlen.
    destruct b1, b2; simpl.
    + apply IH. exact Hlen.
    + right. reflexivity.
    + left. reflexivity.
    + apply IH. exact Hlen.
Qed.

(* The lex constraint as a constraint type: given a boolean list of length 2n,
   check that the first half is lex <= the second half *)
Definition lex_constraint : constraint :=
  fun l => lex_le (firstn (length l / 2) l) (skipn (length l / 2) l).

Theorem lex_constraint_nil : lex_constraint [] = true.
Proof. reflexivity. Qed.

End LexOrderDefs.
