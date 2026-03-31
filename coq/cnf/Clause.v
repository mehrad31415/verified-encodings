(* Clause.v — Boolean disjunctive clauses
   New file for Phase 1 integration (DRP Winter 2026)
   Based on src/cnf/clause.lean by Codel, Avigad, Heule (CMU)
   Some definitions adapted from Linxi's cnf.v *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Import ListNotations.

From VE Require Import cnf.Literal.
From VE Require Import cnf.Assignment.

Set Implicit Arguments.

Section ClauseDefs.

Variable V : Type.

(* A clause is a disjunction of literals *)
Definition clause := list (literal V).

(* Evaluate a clause as a disjunction *)
Definition eval_clause (tau : assignment V) (c : clause) : bool :=
  existsb (eval tau) c.

Theorem eval_clause_nil : forall tau, eval_clause tau [] = false.
Proof. reflexivity. Qed.

Theorem eval_clause_singleton : forall tau (l : literal V),
  eval_clause tau [l] = eval tau l.
Proof.
  intros. unfold eval_clause. simpl. rewrite orb_false_r. reflexivity.
Qed.

Theorem eval_clause_cons : forall tau (l : literal V) (c : clause),
  eval_clause tau (l :: c) = (eval tau l || eval_clause tau c)%bool.
Proof.
  intros. unfold eval_clause. simpl. reflexivity.
Qed.

Theorem eval_clause_tt_iff_exists :
  forall (tau : assignment V) (c : clause),
    eval_clause tau c = true <-> exists l, In l c /\ eval tau l = true.
Proof.
  intros tau c. induction c as [| l ls IH].
  - split.
    + discriminate.
    + intros [l [H _]]. inversion H.
  - rewrite eval_clause_cons. split.
    + intros H. apply orb_true_iff in H. destruct H as [H | H].
      * exists l. split; [left; reflexivity | exact H].
      * apply IH in H. destruct H as [l2 [Hl He]].
        exists l2. split; [right; exact Hl | exact He].
    + intros [l2 [[Heq | Hin] He]].
      * subst. apply orb_true_iff. left. exact He.
      * apply orb_true_iff. right. apply IH. exists l2. split; assumption.
Qed.

Theorem eval_clause_ff_iff_forall :
  forall (tau : assignment V) (c : clause),
    eval_clause tau c = false <-> forall l, In l c -> eval tau l = false.
Proof.
  intros tau c. induction c as [| l ls IH].
  - split.
    + intros _ l H. inversion H.
    + reflexivity.
  - rewrite eval_clause_cons. rewrite orb_false_iff. rewrite IH.
    split.
    + intros [Hl Hls] l2 [Heq | Hin].
      * subst. exact Hl.
      * apply Hls. exact Hin.
    + intros H. split.
      * apply H. left. reflexivity.
      * intros l2 Hl2. apply H. right. exact Hl2.
Qed.

Theorem eval_clause_app : forall (tau : assignment V) (c1 c2 : clause),
  eval_clause tau (c1 ++ c2) = (eval_clause tau c1 || eval_clause tau c2)%bool.
Proof.
  intros tau c1 c2. induction c1 as [| l ls IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite orb_assoc. reflexivity.
Qed.

(* Variables in a clause *)
Definition clause_vars (c : clause) : list V := map (var (V:=V)) c.

Theorem in_clause_vars_iff : forall (v : V) (c : clause),
  In v (clause_vars c) <-> exists l, In l c /\ var l = v.
Proof.
  intros v c. unfold clause_vars. rewrite in_map_iff.
  split; intros [l [H1 H2]]; exists l; tauto.
Qed.

Theorem in_clause_vars_of_mem : forall (c : clause) (l : literal V),
  In l c -> In (var l) (clause_vars c).
Proof.
  intros c l Hl. apply in_clause_vars_iff. exists l. split; [exact Hl | reflexivity].
Qed.

(* Clause eval respects agree_on *)
Theorem eval_clause_eq_of_agree_on :
  forall (tau1 tau2 : assignment V) (c : clause),
    agree_on tau1 tau2 (clause_vars c) ->
    eval_clause tau1 c = eval_clause tau2 c.
Proof.
  intros tau1 tau2 c Hagree.
  induction c as [| l ls IH].
  - reflexivity.
  - rewrite !eval_clause_cons. f_equal.
    + assert (Hv : tau1 (var l) = tau2 (var l)).
      { apply Hagree. simpl. left. reflexivity. }
      destruct l as [v | v]; simpl in *; rewrite Hv; reflexivity.
    + apply IH. intros v Hv. apply Hagree. simpl. right. exact Hv.
Qed.

(* Tautology: if a literal and its flip are both in a clause, it's always true *)
Theorem eval_clause_tautology :
  forall (c : clause) (l : literal V),
    In l c -> In (flip l) c ->
    forall tau, eval_clause tau c = true.
Proof.
  intros c l Hl Hfl tau.
  apply eval_clause_tt_iff_exists.
  destruct (eval tau l) eqn:He.
  - exists l. split; assumption.
  - exists (flip l). split.
    + exact Hfl.
    + rewrite eval_flip. rewrite He. reflexivity.
Qed.

(* Falsify: create a clause from variables that evaluates to false *)
Definition falsify (tau : assignment V) (vars : list V) : clause :=
  map (fun v => if tau v then Neg v else Pos v) vars.

Theorem falsify_eval_ff :
  forall (tau : assignment V) (l : list V),
    eval_clause tau (falsify tau l) = false.
Proof.
  intros tau l. induction l as [| v vs IH].
  - reflexivity.
  - simpl. destruct (tau v) eqn:Hv; simpl; rewrite Hv; simpl; exact IH.
Qed.

Definition truthify (tau : assignment V) (vars : list V) : clause :=
  map (fun v => if tau v then Pos v else Neg v) vars.

Theorem truthify_eval_tt :
  forall (tau : assignment V) (l : list V),
    l <> [] -> eval_clause tau (truthify tau l) = true.
Proof.
  intros tau l Hne. destruct l as [| v vs].
  - contradiction.
  - simpl. destruct (tau v) eqn:Hv; simpl; rewrite Hv; reflexivity.
Qed.

Theorem falsify_map_var_eq :
  forall (tau : assignment V) (l : list V),
    map (var (V:=V)) (falsify tau l) = l.
Proof.
  intros tau l. induction l as [| v vs IH].
  - reflexivity.
  - simpl. destruct (tau v); simpl; f_equal; exact IH.
Qed.

Theorem truthify_map_var_eq :
  forall (tau : assignment V) (l : list V),
    map (var (V:=V)) (truthify tau l) = l.
Proof.
  intros tau l. induction l as [| v vs IH].
  - reflexivity.
  - simpl. destruct (tau v); simpl; f_equal; exact IH.
Qed.

End ClauseDefs.
