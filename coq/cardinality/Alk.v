(* Alk.v — At-least-k Boolean cardinality constraint
   Phase 3 (DRP Winter 2026)
   Based on src/cardinality/alk.lean by Codel, Avigad, Heule (CMU) *)

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
From VE Require Import cardinality.Amk.

Set Implicit Arguments.

(* At-least-k: at least k of the inputs are true *)
Definition alk (k : nat) : constraint := fun l => Nat.leb k (count_occ Bool.bool_dec l true).

Section AlkEval.

Variable V : Type.

Definition alk_eval (k : nat) (tau : assignment V) (l : list (literal V)) : bool :=
  constraint_eval (alk k) tau l.

Theorem alk_eval_zero : forall (tau : assignment V) (l : list (literal V)),
  alk_eval 0 tau l = true.
Proof.
  intros tau l. unfold alk_eval, constraint_eval, alk. simpl. reflexivity.
Qed.

Theorem alk_eval_cons_pos : forall k (tau : assignment V) (lit : literal V) (l : list (literal V)),
  eval tau lit = true ->
  alk_eval (S k) tau (lit :: l) = alk_eval k tau l.
Proof.
  intros k tau lit l Hlit.
  unfold alk_eval, constraint_eval, alk. simpl. rewrite Hlit. simpl.
  reflexivity.
Qed.

Theorem alk_eval_cons_neg : forall k (tau : assignment V) (lit : literal V) (l : list (literal V)),
  eval tau lit = false ->
  alk_eval k tau (lit :: l) = alk_eval k tau l.
Proof.
  intros k tau lit l Hlit.
  unfold alk_eval, constraint_eval, alk. simpl. rewrite Hlit. simpl.
  reflexivity.
Qed.

(* ALO special case: at-least-one *)
Definition alo := alk 1.

(* ALO is true iff there exists a literal that evaluates to true *)
Theorem alo_eval_tt_iff_exists_tt :
  forall (tau : assignment V) (l : list (literal V)),
    alk_eval 1 tau l = true <-> exists lit, In lit l /\ eval tau lit = true.
Proof.
  intros tau l. induction l as [| lit ls IH].
  - split.
    + unfold alk_eval, constraint_eval, alk. simpl. discriminate.
    + intros [lit [H _]]. inversion H.
  - split.
    + intro H. destruct (eval tau lit) eqn:Hlit.
      * exists lit. split; [left; reflexivity | exact Hlit].
      * rewrite alk_eval_cons_neg in H; auto.
        apply IH in H. destruct H as [lit2 [Hin Heval]].
        exists lit2. split; [right; exact Hin | exact Heval].
    + intros [lit2 [Hmem Heval]].
      destruct Hmem as [Heq | Hin].
      { subst. unfold alk_eval, constraint_eval, alk. simpl. rewrite Heval. simpl. reflexivity. }
      { destruct (eval tau lit) eqn:Hlit.
        - unfold alk_eval, constraint_eval, alk. simpl. rewrite Hlit. simpl. reflexivity.
        - rewrite alk_eval_cons_neg; auto. apply IH.
          exists lit2. split; assumption. }
Qed.

(* Direct ALO encoding: just the clause itself *)
Definition direct_alo : enc_fn V := dir_enc (fun l => [l]).

Theorem direct_alo_encodes_alo :
  encodes (alk 1) direct_alo.
Proof.
  split.
  - (* correctness *)
    intros l g Hdisj tau. split.
    + intro Halo.
      exists tau. split.
      * unfold direct_alo, dir_enc. simpl.
        change (eval_cnf tau [l]) with (forallb (eval_clause tau) [l]).
        simpl. rewrite andb_true_r.
        apply alo_eval_tt_iff_exists_tt in Halo.
        destruct Halo as [lit [Hin Heval]].
        apply eval_clause_tt_iff_exists. exists lit. split; assumption.
      * apply agree_on_refl.
    + intros [sigma [Heval Hagree]].
      unfold direct_alo, dir_enc in Heval. simpl in Heval.
      change (eval_cnf sigma [l]) with (forallb (eval_clause sigma) [l]) in Heval.
      simpl in Heval. rewrite andb_true_r in Heval.
      apply alo_eval_tt_iff_exists_tt.
      apply eval_clause_tt_iff_exists in Heval.
      destruct Heval as [lit [Hin Heval]].
      exists lit. split; [exact Hin |].
      assert (Hvar : In (var lit) (clause_vars l)).
      { apply in_clause_vars_of_mem. exact Hin. }
      destruct lit as [v | v]; simpl in *.
      * rewrite (Hagree v Hvar). exact Heval.
      * rewrite (Hagree v Hvar). exact Heval.
  - (* well-behavedness *)
    intros l g Hdisj. split.
    + intros a Ha. exact Ha.
    + intros v Hv. left.
      unfold direct_alo, dir_enc in Hv. simpl in Hv.
      rewrite app_nil_r in Hv. exact Hv.
Qed.

End AlkEval.
