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
  disjoint l g -> v in l -> v not in g.
Proof.
    intros l g v Hdisjoint Hin.
    unfold disjoint in Hdisjoint.
    apply Hdisjoint.
    apply Hin.
Qed.

Theorem disjoint_right: forall (1: list (literal V)) (2: gensym V) (3: V), disjoint 1 2 -> 3 in 1 -> 3 not in 2.
Proof.
    intros 1 2 3 Hdisjoint Hin.
    unfold disjoint in Hdisjoint.
    apply Hdisjoint.
    apply Hin.
Qed.

Theorem disjoint_perm: forall (1: list (literal V)) (2: gensym V) (3: list (literal V)), disjoint 1 2 -> 3 perm 1 -> disjoint 3 2.
Proof.
    intros 1 2 3 Hdisjoint Hperm.
    unfold disjoint in Hdisjoint.
    apply Hdisjoint.
    apply Hperm.
Qed.

Namespace constraint.
Variable C: constraint V.
Parameter eval: constraint V -> assignment V -> list (Literal V) -> bool.

Theorem eval_eq_of_agree_on: forall (1: assignment V) (2: assignment V) (3: list (literal V)), agree_on 1 2 (clause.vars 3) -> eval C 1 3 = 2.
Proof.
    intros 1 2 3 Hagree.
    unfold eval in Hagree.
    apply Hagree.
Qed.

Theorem append_id_left_id: forall (1: constraint V), append_id ++ C = C.
Proof.
    intros 1.
    unfold append_id.
    unfold append.
    apply eval_eq_of_agree_on.
    apply agree_on_id.
Qed.

Theorem append_id_right_id: forall (1: constraint V), C ++ append_id = C.
Proof.
    intros 1.
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

Theorem append_comm: forall (1: constraint V) (2: constraint V), 1 ++ 2 = 2 ++ 1.
Proof.
    intros 1 2.
    unfold append.
    apply eval_eq_of_agree_on.
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
  (c1 ++ c2).eval tau l = true <-> c1.eval tau l = true /\ c2.eval tau l = true.
Proof.
  unfold constraint_eval, eval.
  unfold append.
  rewrite andb_true_iff.
  split; intros H; destruct H as [H1 H2]; split; assumption.
Qed.

Parameter fold (1: list constraint) := 1.foldr append append_id.\

Theorem fold_nil (fold[]): append_id := rfl.

Theorem fold_singleton: fold [enc] = enc by simp [fold].

Theorem fold_cons (1: list (enc_fn V)): fold (enc : 1) = enc ++ fold 1 by simp.

Parameter formula_encodes: forall (1: list (literal V)) (g), disjoint 
