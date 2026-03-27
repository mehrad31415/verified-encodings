(* Import required modules for encoding definitions and utilities *)
(* Note: The following modules must exist and be accessible to Coq for these Requires to work. 
   If you see errors, ensure the corresponding .v files are present and the load path is set. *)
Require Import assignment.
Require Import clause.
Require Import cnf.
Require Import gensym.
Require Import literal.
From LF Require Export Basics.


Variable V: Type.
Variable constraint: Type -> bool.
Parameter enc: list (literal V) -> gensym V -> cnf V * gensym V.
Parameter disjoint: list (literal V) -> gensym V -> Prop.

Theorem disjoint_left: forall (l: list (literal V)) (g: gensym V) (v: V),
  disjoint l g -> In v (map (@literal.var V) l) -> ~ In v (gensym.stock g).
Proof.
  intros l g v Hdisjoint Hin.
  unfold disjoint in Hdisjoint.
  apply Hdisjoint.
  assumption.
Qed.

Theorem disjoint_right: forall (l: list (literal V)) (g: gensym V) (v: V),
  disjoint l g -> In v (gensym.stock g) -> ~ In v (map (@literal.var V) l).
Proof.
  intros l g v Hdisjoint Hin.
  unfold disjoint in Hdisjoint.
  intro Hcontra.
  apply (Hdisjoint Hcontra) in Hin.
  assumption.
Qed.

Theorem disjoint_perm: forall (l1: list (literal V)) (g: gensym V) (l2: list (literal V)), disjoint l1 g -> Permutation l2 l1 -> disjoint l2 g.
Proof.
  intros l1 g l2 Hdisjoint Hperm v Hvin.
  apply Hdisjoint.
  apply Permutation_in with (l':=l2) (l:=l1) in Hvin; auto.
Qed.

Module constraint.
Variable C: constraint V.
Parameter eval: constraint V -> assignment V -> list (literal V) -> bool.

Theorem eval_eq_of_agree_on: forall (a1: assignment V) (a2: assignment V) (l: list (literal V)),
  agree_on a1 a2 (clause.vars l) -> eval C a1 l = eval C a2 l.
Proof.
  (* Detailed proof would depend on the definition of eval and agree_on;
     placeholder for now. *)
Admitted.

End constraint.

Theorem append_id_left_id: forall (l: constraint V), append_id ++ C = C.
Proof.
    intros l.
    unfold append_id.
    unfold append.
    apply eval_eq_of_agree_on.
    apply agree_on_id.
Qed.

Theorem append_id_right_id: forall (l: constraint V), C ++ append_id = C.
Proof.
    intros l.
    unfold append_id. 
    unfold append.
    apply eval_eq_of_agree_on. 
    apply agree_on_id.
Qed.

Instance is_left: is_left_id (constraint V) has_append append_id.
Proof.
    apply Build_is_left_id.
    apply append_id_left_id.
Qed.

Instance is_right_id: is_right_id (constraint V) has_append append_id.
Proof.
    apply Build_is_right_id.
    apply append_id_right_id.
Qed.

Theorem append_comm: forall (c1 c2: constraint V), c1 ++ c2 = c2 ++ c1.
Proof.
  intros c1 c2.
  unfold append.
  apply constraint.eval_eq_of_agree_on.
  apply agree_on_comm.
Qed.

Theorem append_tt_iff (c1 c2 : constraint V) (l : list (Literal V)) : (c1 ++ c2) l = true <-> c1 l = true /\ c2 l = true.
Proof.
  unfold append.
  split; intros H.
  - apply andb_true_iff in H. destruct H as [H1 H2]. split; assumption.
  - destruct H as [H1 H2]. apply andb_true_iff. split; assumption.
Qed.

Theorem append_eval_tt_iff (c1 c2 : constraint V) (l : list (Literal V)) (tau : assignment V) :
  (constraint.append c1 c2) eval tau l = true <-> c1.eval tau l = true /\ c2.eval tau l = true
Proof.
  unfold constraint_eval, eval.
  unfold append.
  rewrite andb_true_iff.
  split; intros H; destruct H as [H1 H2]; split; assumption.
Qed.

Instance is_left_id: is_left_id (constraint V) has_append append_id.
Proof.
    apply Build_is_left_id.
    apply append_id_left_id.
Qed.


Instance is_right_id: is_right_id (constraint V) has_append append_id.
Proof.
    apply Build_is_right_id.
    apply append_id_right_id.
Qed.

Definition fold (l : list (constraint V)) : constraint V := List.fold_right append append_id l.

Theorem fold_nil (l: list (constrain V)): append_id.
Proof.
    reflexivity.
Qed.
    
Theorem fold_singleton (fold(enc)): enc := by simp [fold].
Theorem fold_cons (enc: constraint V) (l: list (constraint V)) : fold (enc :: l) = enc ++ fold l.
Proof.
  unfold fold.
  simpl.
  reflexivity.
Qed.

(* is_correct: An encoding function is correct if, whenever the input literals and the gensym are disjoint,
   the CNF constraint returned by enc encodes the function on the input literals. *)
Definition is_correct
  (enc : list (literal V) -> gensym V -> (constraint V * gensym V)) : Prop :=
  forall (l : list (literal V)) (g : gensym V),
    disjoint l g ->
    formula_encodes ((enc l g).1) l.

(* is_well_behaved: An encoding is well-behaved if it only introduces fresh variables,
   that is, the only variables in the output are from the input literals or from the gensym's stock,
   and no other variables are introduced. *)
Definition is_well_behaved
  (enc : list (literal V) -> gensym V -> (constraint V * gensym V)) : Prop :=
  forall (l : list (literal V)) (g : gensym V),
    disjoint l g ->
      (* All new gensym variables are a subset of the original gensym stock *)
      subset ((enc l g).2).stock g.stock /\
      (* All variables in the constraint are from the input literals or new gensym variables *)
      subset (vars_of_constraint ((enc l g).1))
             (vars_of_literals l ∪ (g.stock \ ((enc l g).2).stock)).

(* If enc is well-behaved, then no variable outside the input literals or the gensym stock
   appears in the output constraint. *)
Theorem not_mem_form_of_is_wb :
  forall (enc : list (literal V) -> gensym V -> (constraint V * gensym V)),
  is_well_behaved enc ->
  forall (l : list (literal V)) (g : gensym V),
    disjoint l g ->
    forall v,
      ~ (In v (vars_of_literals l) \/ In v g.stock) ->
      ~ In v (vars_of_constraint ((enc l g).1)).
Proof.
  intros enc Hwb l g Hdis v Hnin Hmem.
  specialize (Hwb l g Hdis) as [_ Hvars].
  unfold subset in Hvars.
  apply Hvars in Hmem.
  destruct Hmem as [Hlit | Hstock].
  - apply Hnin. left. assumption.
  - apply Hnin. right. destruct Hstock as [Hinstock _]. assumption.
Qed.
