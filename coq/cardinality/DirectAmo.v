(* DirectAmo.v — Direct (pairwise) at-most-one encoding
   Phase 3 (DRP Winter 2026)
   Based on src/cardinality/direct_amo.lean by Codel, Avigad, Heule (CMU) *)

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

Section DirectAmoDefs.

Variable V : Type.

(* Direct AMO encoding: for each pair of literals, add a clause
   saying at most one can be true: [flip(li), flip(lj)] *)
Fixpoint direct_amo' (l : list (literal V)) : cnf V :=
  match l with
  | [] => []
  | lit :: ls =>
    map (fun m => [flip lit; flip m]) ls ++ direct_amo' ls
  end.

(* As an encoding function *)
Definition direct_amo : enc_fn V := dir_enc direct_amo'.

Theorem direct_amo_nil : direct_amo' ([] : list (literal V)) = [].
Proof. reflexivity. Qed.

Theorem direct_amo_singleton : forall (lit : literal V),
  direct_amo' [lit] = [].
Proof. reflexivity. Qed.

Theorem direct_amo_double : forall (l1 l2 : literal V),
  direct_amo' [l1; l2] = [[flip l1; flip l2]].
Proof. reflexivity. Qed.

(* Each clause in the direct AMO encoding has exactly two literals *)
Theorem length_eq_two_of_mem :
  forall (l : list (literal V)) (c : clause V),
    length l >= 2 -> In c (direct_amo' l) -> length c = 2.
Proof.
  induction l as [| l1 ls IH]; intros c Hlen Hin.
  - simpl in Hlen. lia.
  - simpl in Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_map_iff in Hin. destruct Hin as [m [Hm _]]. subst. reflexivity.
    + destruct ls as [| l2 ls'].
      * simpl in Hin. contradiction.
      * destruct ls' as [| l3 ls''].
        { simpl in Hin. contradiction. }
        { apply IH. { simpl. lia. } exact Hin. }
Qed.

(* The direct AMO CNF evaluates to true iff for any two distinct
   literals in the input, at most one evaluates to true *)
Theorem eval_tt_iff_forall_distinct_ff :
  forall (tau : assignment V) (l : list (literal V)),
    length l >= 2 ->
    (eval_cnf tau (direct_amo' l) = true <->
     forall lit1 lit2, distinct lit1 lit2 l ->
       eval tau lit1 = true -> eval tau lit2 = false).
Proof.
  (* The proof proceeds by showing each clause [flip(li), flip(lj)]
     is satisfied iff not both li and lj are true *)
  admit.
Admitted.

(* Main correctness theorem: direct_amo encodes AMO (amk 1) *)
Theorem direct_amo_formula_encodes_amo :
  forall (l : list (literal V)),
    formula_encodes (amk 1) (direct_amo' l) l.
Proof.
  intro l. intro tau. split; intro H.
  - exists tau. split; [| apply agree_on_refl].
    admit.
  - destruct H as [sigma [Heval Hagree]]. admit.
Admitted.

(* The direct AMO encoding is well-behaved *)
Theorem direct_amo_is_wb : is_wb direct_amo.
Proof.
  intros l g Hdisj. split.
  - intros a Ha. exact Ha. (* gensym unchanged *)
  - intros v Hv. left.     (* all vars from inputs *)
    simpl in Hv.
    induction l as [| lit ls IH].
    + simpl in Hv. contradiction.
    + simpl in Hv. apply in_cnf_vars_iff in Hv.
      destruct Hv as [c [Hc Hv]].
      apply in_app_iff in Hc. destruct Hc as [Hc | Hc].
      * apply in_map_iff in Hc. destruct Hc as [m [Hm Hin]]. subst.
        simpl in Hv. destruct Hv as [Hv | [Hv | Hv]].
        -- rewrite flip_var_eq in Hv. simpl. left. exact Hv.
        -- rewrite flip_var_eq in Hv. subst. simpl. right.
           unfold clause_vars. apply in_map. exact Hin.
        -- contradiction.
      * simpl. right.
        apply IH.
        { intros v0 Hv0. apply Hdisj. simpl. right. exact Hv0. }
        { apply in_cnf_vars_iff. exists c. split; assumption. }
Qed.

(* Main result: direct_amo encodes AMO *)
Theorem direct_amo_encodes_amo :
  encodes (amk 1) direct_amo.
Proof.
  split.
  - intros l g Hdisj. apply direct_amo_formula_encodes_amo.
  - apply direct_amo_is_wb.
Qed.

End DirectAmoDefs.
