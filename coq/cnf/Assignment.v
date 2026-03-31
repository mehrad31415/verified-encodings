(* Assignment.v — Properties of assignments on variables
   Original Coq implementation by Tianyi (Phase 1, DRP Winter 2026)
   Converted from mathcomp to standard Coq library.
   Based on src/cnf/assignment.lean by Codel, Avigad, Heule (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
Import ListNotations.

From VE Require Import cnf.Literal.

Set Implicit Arguments.

Section AgreeOn.

Variable V : Type.

(* Agreement on a set of variables (represented as a list) *)
Definition agree_on (tau1 tau2 : assignment V) (s : list V) : Prop :=
  forall v, In v s -> tau1 v = tau2 v.

(* Constant assignments *)
Definition all_tt : assignment V := fun _ => true.
Definition all_ff : assignment V := fun _ => false.

Theorem all_tt_eval_tt : forall (v : V), all_tt v = true.
Proof. reflexivity. Qed.

Theorem all_ff_eval_ff : forall (v : V), all_ff v = false.
Proof. reflexivity. Qed.

Theorem agree_on_refl : forall (tau : assignment V) (s : list V),
  agree_on tau tau s.
Proof. intros tau s v _. reflexivity. Qed.

Theorem agree_on_symm : forall (tau1 tau2 : assignment V) (s : list V),
  agree_on tau1 tau2 s -> agree_on tau2 tau1 s.
Proof. intros tau1 tau2 s H v Hv. symmetry. apply H. exact Hv. Qed.

Theorem agree_on_comm : forall (tau1 tau2 : assignment V) (s : list V),
  agree_on tau1 tau2 s <-> agree_on tau2 tau1 s.
Proof. intros. split; apply agree_on_symm. Qed.

Theorem agree_on_trans : forall (tau1 tau2 tau3 : assignment V) (s : list V),
  agree_on tau1 tau2 s -> agree_on tau2 tau3 s -> agree_on tau1 tau3 s.
Proof. intros tau1 tau2 tau3 s H1 H2 v Hv. rewrite H1; auto. Qed.

Theorem agree_on_nil : forall (tau1 tau2 : assignment V),
  agree_on tau1 tau2 [].
Proof. intros tau1 tau2 v Hv. inversion Hv. Qed.

Theorem agree_on_subset : forall (tau1 tau2 : assignment V) (s1 s2 : list V),
  (forall v, In v s1 -> In v s2) -> agree_on tau1 tau2 s2 -> agree_on tau1 tau2 s1.
Proof. intros tau1 tau2 s1 s2 Hsub Hs2 v Hv. apply Hs2. apply Hsub. exact Hv. Qed.

Theorem agree_on_app : forall (tau1 tau2 : assignment V) (s1 s2 : list V),
  agree_on tau1 tau2 s1 -> agree_on tau1 tau2 s2 ->
  agree_on tau1 tau2 (s1 ++ s2).
Proof.
  intros tau1 tau2 s1 s2 H1 H2 v Hv.
  apply in_app_iff in Hv. destruct Hv; auto.
Qed.

Theorem agree_on_app_left : forall (tau1 tau2 : assignment V) (s1 s2 : list V),
  agree_on tau1 tau2 (s1 ++ s2) -> agree_on tau1 tau2 s1.
Proof. intros tau1 tau2 s1 s2 H v Hv. apply H. apply in_or_app. left. exact Hv. Qed.

Theorem agree_on_app_right : forall (tau1 tau2 : assignment V) (s1 s2 : list V),
  agree_on tau1 tau2 (s1 ++ s2) -> agree_on tau1 tau2 s2.
Proof. intros tau1 tau2 s1 s2 H v Hv. apply H. apply in_or_app. right. exact Hv. Qed.

(* Evaluation respects agree_on *)
Theorem eval_eq_of_agree_on_of_var_mem :
  forall (tau1 tau2 : assignment V) (s : list V) (l : literal V),
    agree_on tau1 tau2 s -> In (var l) s ->
    eval tau1 l = eval tau2 l.
Proof.
  intros tau1 tau2 s l Hagree Hin.
  destruct l as [v | v]; simpl in *.
  - apply Hagree. exact Hin.
  - f_equal. apply Hagree. exact Hin.
Qed.

End AgreeOn.

Section Aite.

Variable V : Type.
Hypothesis V_eq_dec : forall (x y : V), {x = y} + {x <> y}.

(* Assignment if-then-else: use tau1 for variables in s, tau2 otherwise *)
Definition aite (s : list V) (tau1 tau2 : assignment V) : assignment V :=
  fun v => if in_dec V_eq_dec v s then tau1 v else tau2 v.

Theorem aite_pos : forall (s : list V) (v : V) (tau1 tau2 : assignment V),
  In v s -> aite s tau1 tau2 v = tau1 v.
Proof.
  intros s v tau1 tau2 Hv. unfold aite.
  destruct (in_dec V_eq_dec v s); [ reflexivity | contradiction ].
Qed.

Theorem aite_neg : forall (s : list V) (v : V) (tau1 tau2 : assignment V),
  ~ In v s -> aite s tau1 tau2 v = tau2 v.
Proof.
  intros s v tau1 tau2 Hv. unfold aite.
  destruct (in_dec V_eq_dec v s); [ contradiction | reflexivity ].
Qed.

Theorem aite_agree_on : forall (s : list V) (tau1 tau2 : assignment V),
  agree_on (aite s tau1 tau2) tau1 s.
Proof.
  intros s tau1 tau2 v Hv. apply aite_pos. exact Hv.
Qed.

End Aite.
