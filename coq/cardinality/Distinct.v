(* Distinct.v — Two distinct positions in a list
   Phase 3 (DRP Winter 2026)
   Based on src/cardinality/distinct.lean by Codel (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Import ListNotations.

Set Implicit Arguments.

Section DistinctDefs.

Variable A : Type.

(* Two elements at different indices in a list *)
Definition distinct (a1 a2 : A) (l : list A) : Prop :=
  exists i j,
    i < j /\ j < length l /\
    nth_error l i = Some a1 /\ nth_error l j = Some a2.

Theorem not_distinct_nil : forall (a1 a2 : A), ~ distinct a1 a2 [].
Proof.
  intros a1 a2 [i [j [Hij [Hj _]]]]. simpl in Hj. lia.
Qed.

Theorem not_distinct_singleton : forall (a1 a2 a3 : A), ~ distinct a1 a2 [a3].
Proof.
  intros a1 a2 a3 [i [j [Hij [Hj _]]]]. simpl in Hj. lia.
Qed.

Theorem distinct_double : forall (a1 a2 : A),
  distinct a1 a2 [a1; a2].
Proof.
  intros a1 a2.
  exists 0, 1. repeat split; simpl; auto; lia.
Qed.

Theorem distinct_cons_of_mem : forall (a1 : A) (a2 : A) (l : list A),
  In a2 l -> distinct a1 a2 (a1 :: l).
Proof.
  intros a1 a2 l Hin.
  apply In_nth_error in Hin. destruct Hin as [n Hn].
  exists 0, (S n). simpl. split; [lia |]. split.
  - enough (n < length l) by lia.
    apply nth_error_Some. rewrite Hn. discriminate.
  - split; [reflexivity | exact Hn].
Qed.

Theorem distinct_cons_of_distinct : forall (a : A) (a1 a2 : A) (l : list A),
  distinct a1 a2 l -> distinct a1 a2 (a :: l).
Proof.
  intros a a1 a2 l [i [j [Hij [Hj [Hil Hjl]]]]].
  exists (S i), (S j). simpl. repeat split; try lia.
  - exact Hil.
  - exact Hjl.
Qed.

Theorem mem_of_distinct_left : forall (a1 a2 : A) (l : list A),
  distinct a1 a2 l -> In a1 l.
Proof.
  intros a1 a2 l [i [j [Hij [Hj [Hil Hjl]]]]].
  apply nth_error_In in Hil. exact Hil.
Qed.

Theorem mem_of_distinct_right : forall (a1 a2 : A) (l : list A),
  distinct a1 a2 l -> In a2 l.
Proof.
  intros a1 a2 l [i [j [Hij [Hj [Hil Hjl]]]]].
  apply nth_error_In in Hjl. exact Hjl.
Qed.

End DistinctDefs.
