(* Gensym.v — Fresh variable generator for CNF encodings
   Original Coq implementation by Manvi (Phase 1, DRP Winter 2026)
   Fixed syntax errors and completed proofs.
   Based on src/cnf/gensym.lean by Codel, Avigad, Heule (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Import ListNotations.

From VE Require Import cnf.Literal.

Set Implicit Arguments.

Section GensymDefs.

Variable A : Type.

(* A gensym tracks a position on the natural number line.
   When provided with an injective function from nats to the variable type,
   it provably generates fresh variables. *)
Record gensym := mk_gensym {
  offset : nat;
  f : nat -> A;
  f_inj : forall x y, f x = f y -> x = y
}.

(* Generate a fresh variable and return an updated gensym *)
Definition fresh (g : gensym) : A * gensym :=
  (g.(f) g.(offset),
   mk_gensym (S g.(offset)) g.(f) g.(f_inj)).

Theorem fresh_var : forall (g : gensym),
  fst (fresh g) = g.(f) g.(offset).
Proof. intro g. reflexivity. Qed.

Theorem fresh_offset : forall (g : gensym),
  offset (snd (fresh g)) = S (offset g).
Proof. intro g. reflexivity. Qed.

Theorem fresh_f : forall (g : gensym),
  f (snd (fresh g)) = f g.
Proof. intro g. reflexivity. Qed.

(* Generate n fresh variables - simpler non-destructuring version *)
Fixpoint nfresh_aux (func : nat -> A) (start n : nat) : list A :=
  match n with
  | 0 => []
  | S n' => func start :: nfresh_aux func (S start) n'
  end.

Definition nfresh (g : gensym) (n : nat) : list A * gensym :=
  (nfresh_aux g.(f) g.(offset) n,
   mk_gensym (g.(offset) + n) g.(f) g.(f_inj)).

Theorem nfresh_zero : forall (g : gensym),
  fst (nfresh g 0) = [].
Proof. intro g. reflexivity. Qed.

Theorem length_nfresh : forall (g : gensym) (n : nat),
  length (fst (nfresh g n)) = n.
Proof.
  intros g n. unfold nfresh. simpl.
  revert g. induction n as [| n' IH]; intro g.
  - reflexivity.
  - simpl. f_equal. apply (IH (mk_gensym (S (offset g)) (f g) (f_inj g))).
Qed.

Theorem nfresh_offset : forall (g : gensym) (n : nat),
  offset (snd (nfresh g n)) = offset g + n.
Proof. intros. reflexivity. Qed.

Theorem nfresh_f : forall (g : gensym) (n : nat),
  f (snd (nfresh g n)) = f g.
Proof. intros. reflexivity. Qed.

(* The stock of a gensym: all variables it can produce *)
Definition stock (g : gensym) (a : A) : Prop :=
  exists n, g.(f) (g.(offset) + n) = a.

Theorem fresh_in_stock : forall (g : gensym),
  stock g (fst (fresh g)).
Proof.
  intro g. exists 0. simpl. rewrite Nat.add_0_r. reflexivity.
Qed.

(* nth variable from a gensym *)
Definition nth_var (g : gensym) (n : nat) : A := g.(f) (g.(offset) + n).

Theorem nth_var_ne_of_ne : forall (g : gensym) (i j : nat),
  i <> j -> nth_var g i <> nth_var g j.
Proof.
  intros g i j Hne Heq. apply Hne.
  unfold nth_var in Heq. apply g.(f_inj) in Heq. lia.
Qed.

Theorem nth_var_zero_eq_fresh : forall (g : gensym),
  nth_var g 0 = fst (fresh g).
Proof.
  intro g. unfold nth_var. simpl. rewrite Nat.add_0_r. reflexivity.
Qed.

Theorem nth_var_in_stock : forall (g : gensym) (n : nat),
  stock g (nth_var g n).
Proof.
  intros g n. exists n. reflexivity.
Qed.

(* Fresh stock is a subset of the original stock *)
Theorem fresh_stock_subset : forall (g : gensym) (a : A),
  stock (snd (fresh g)) a -> stock g a.
Proof.
  intros g a [n Hn]. exists (S n). simpl in Hn.
  rewrite Nat.add_succ_r. exact Hn.
Qed.

(* A fresh variable is not in the updated gensym's stock *)
Theorem fresh_not_in_fresh_stock : forall (g : gensym),
  ~ stock (snd (fresh g)) (fst (fresh g)).
Proof.
  intros g [n Hn]. simpl in Hn.
  apply g.(f_inj) in Hn. lia.
Qed.

(* Disjointness: stock and a list of variables *)
Definition disj_stock (g : gensym) (vars : list A) : Prop :=
  forall v, In v vars -> ~ stock g v.

End GensymDefs.
