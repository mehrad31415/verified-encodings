(* Cnf.v — Conjunctive Normal Form formulas
   Original Coq implementation by Linxi (Phase 1, DRP Winter 2026)
   Based on src/cnf/cnf.lean by Codel, Avigad, Heule (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Import ListNotations.

From VE Require Import cnf.Literal.
From VE Require Import cnf.Assignment.
From VE Require Import cnf.Clause.

Set Implicit Arguments.

Section CnfDefs.

Variable V : Type.

(* A CNF formula is a conjunction (list) of clauses *)
Definition cnf := list (clause V).

(* Evaluate a CNF formula: conjunction of all clauses *)
Definition eval_cnf (tau : assignment V) (f : cnf) : bool :=
  forallb (eval_clause tau) f.

Theorem eval_cnf_nil : forall tau, eval_cnf tau ([] : cnf) = true.
Proof. reflexivity. Qed.

Theorem eval_cnf_singleton : forall tau (c : clause V),
  eval_cnf tau [c] = eval_clause tau c.
Proof.
  intros. unfold eval_cnf. simpl. rewrite andb_true_r. reflexivity.
Qed.

Theorem eval_cnf_cons : forall tau (c : clause V) (f : cnf),
  eval_cnf tau (c :: f) = (eval_clause tau c && eval_cnf tau f)%bool.
Proof.
  intros. unfold eval_cnf. simpl. reflexivity.
Qed.

Theorem eval_cnf_app : forall (tau : assignment V) (f1 f2 : cnf),
  eval_cnf tau (f1 ++ f2) = (eval_cnf tau f1 && eval_cnf tau f2)%bool.
Proof.
  intros tau f1 f2. unfold eval_cnf. rewrite forallb_app. reflexivity.
Qed.

Theorem eval_cnf_tt_iff_forall :
  forall (tau : assignment V) (f : cnf),
    eval_cnf tau f = true <-> (forall c, In c f -> eval_clause tau c = true).
Proof.
  intros tau f. induction f as [| c cs IH].
  - split; simpl; intros; try contradiction; auto.
  - rewrite eval_cnf_cons. rewrite andb_true_iff. rewrite IH.
    split.
    + intros [Hc Hcs] c0 [H | H].
      * subst. assumption.
      * apply Hcs. assumption.
    + intros H. split.
      * apply H. left. reflexivity.
      * intros c0 Hc0. apply H. right. assumption.
Qed.

Theorem eval_cnf_ff_iff_exists :
  forall (tau : assignment V) (f : cnf),
    eval_cnf tau f = false <-> (exists c, In c f /\ eval_clause tau c = false).
Proof.
  intros tau f. induction f as [| c cs IH].
  - split.
    + discriminate.
    + intros [c [H _]]. inversion H.
  - rewrite eval_cnf_cons. rewrite andb_false_iff. rewrite IH.
    split.
    + intros [Hc | Hcs].
      * exists c. split; [left; reflexivity | assumption].
      * destruct Hcs as [c' [Hinc' Hff']].
        exists c'. split; [right; assumption | assumption].
    + intros [c' [[H | H] Hff]].
      * subst. left. assumption.
      * right. exists c'. split; assumption.
Qed.

(* Satisfiability *)
Definition satisfiable (f : cnf) := exists tau, eval_cnf tau f = true.

Theorem satisfiable_of_eval_tt :
  forall (f : cnf) (tau : assignment V), eval_cnf tau f = true -> satisfiable f.
Proof.
  intros f tau H. exists tau. exact H.
Qed.

(* Variables in a CNF formula *)
Fixpoint cnf_vars (f : cnf) : list V :=
  match f with
  | [] => []
  | c :: cs => clause_vars c ++ cnf_vars cs
  end.

Theorem cnf_vars_nil : cnf_vars ([] : cnf) = [].
Proof. reflexivity. Qed.

Theorem cnf_vars_cons : forall (c : clause V) (f : cnf),
  cnf_vars (c :: f) = clause_vars c ++ cnf_vars f.
Proof. reflexivity. Qed.

Theorem cnf_vars_app : forall (f1 f2 : cnf),
  cnf_vars (f1 ++ f2) = cnf_vars f1 ++ cnf_vars f2.
Proof.
  induction f1 as [| c cs IH]; intro f2.
  - reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Theorem in_cnf_vars_iff :
  forall (v : V) (f : cnf),
    In v (cnf_vars f) <-> exists c, In c f /\ In v (clause_vars c).
Proof.
  intros v f. induction f as [| c cs IH].
  - simpl. split.
    + intro H. contradiction.
    + intros [c [H _]]. inversion H.
  - simpl. rewrite in_app_iff. rewrite IH.
    split.
    + intros [Hv | [c' [Hinc' Hv]]].
      * exists c. split; [left; reflexivity | assumption].
      * exists c'. split; [right; assumption | assumption].
    + intros [c' [[H | H] Hv]].
      * subst. left. assumption.
      * right. exists c'. split; assumption.
Qed.

Theorem clause_vars_subset_cnf_vars :
  forall (c : clause V) (f : cnf),
    In c f -> forall v, In v (clause_vars c) -> In v (cnf_vars f).
Proof.
  intros c f Hc v Hv.
  apply in_cnf_vars_iff. exists c. split; assumption.
Qed.

(* CNF eval respects agree_on *)
Theorem eval_cnf_eq_of_agree_on :
  forall (tau1 tau2 : assignment V) (f : cnf),
    agree_on tau1 tau2 (cnf_vars f) ->
    eval_cnf tau1 f = eval_cnf tau2 f.
Proof.
  intros tau1 tau2 f Hagree.
  induction f as [| c cs IH].
  - reflexivity.
  - rewrite !eval_cnf_cons. f_equal.
    + apply eval_clause_eq_of_agree_on.
      intros v Hv. apply Hagree. simpl. apply in_or_app. left. exact Hv.
    + apply IH. intros v Hv. apply Hagree. simpl. apply in_or_app. right. exact Hv.
Qed.

(* Counting *)
Definition count_tt_cnf (tau : assignment V) (f : cnf) : nat :=
  length (filter (fun c => eval_clause tau c) f).

Definition count_ff_cnf (tau : assignment V) (f : cnf) : nat :=
  length (filter (fun c => negb (eval_clause tau c)) f).

(* Equisatisfiability *)
Definition eqsat (f1 f2 : cnf) := satisfiable f1 <-> satisfiable f2.

Theorem eqsat_refl : forall (f : cnf), eqsat f f.
Proof. intro f. split; auto. Qed.

Theorem eqsat_symm : forall (f1 f2 : cnf), eqsat f1 f2 -> eqsat f2 f1.
Proof. intros f1 f2 [H1 H2]. split; assumption. Qed.

Theorem eqsat_trans : forall (f1 f2 f3 : cnf),
  eqsat f1 f2 -> eqsat f2 f3 -> eqsat f1 f3.
Proof.
  intros f1 f2 f3 [H12 H21] [H23 H32]. split; auto.
Qed.

(* S-equivalence: stronger than equisatisfiability *)
Definition sequiv (f1 f2 : cnf) (s : list V) :=
  forall tau,
    (exists sigma1, eval_cnf sigma1 f1 = true /\ agree_on tau sigma1 s) <->
    (exists sigma2, eval_cnf sigma2 f2 = true /\ agree_on tau sigma2 s).

Theorem sequiv_refl : forall (f : cnf) (s : list V), sequiv f f s.
Proof. intros f s tau. split; auto. Qed.

Theorem sequiv_symm : forall (f1 f2 : cnf) (s : list V),
  sequiv f1 f2 s -> sequiv f2 f1 s.
Proof. intros f1 f2 s H tau. split; apply H. Qed.

End CnfDefs.
