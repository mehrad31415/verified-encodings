Require Import literal.
Require Import clause.

Require Import List.
Require Import Bool.
Require Import ListDec.
Require Import Setoid.
Require Import Morphisms.
Import ListNotations.


Section CNF_Definition.

Variable V : Type. 

 

Hypothesis V_eq_dec : forall x y : V, {x = y} + {x <> y}.


Definition cnf := list clause.

Definition assignment := V -> bool.



Definition eval_literal (τ : assignment) (l : literal) : bool :=
  match l with
  | Pos v => τ v
  | Neg v => negb (τ v)
  end.

Definition eval_clause (τ : assignment) (c : clause) : bool :=
  existsb (eval_literal τ) c.

// starting from protected def from line 68
Definition eval_cnf (τ : assignment) (f : cnf) : bool :=
  fold_right (fun c b => b && (eval_clause τ c)) true f.



Theorem eval_nil : forall τ, eval_cnf τ [] = true.
Proof. reflexivity. Qed.

Theorem eval_singleton : forall τ c, eval_cnf τ [c] = eval_clause τ c.
Proof. intros. simpl. apply andb_true_r. Qed.

Theorem eval_cons : forall τ c f, eval_cnf τ (c :: f) = eval_clause τ c && eval_cnf τ f.
Proof. intros. simpl. apply creativity, andb_comm. Qed.

// from line 79 
Theorem eval_tt_iff_forall_clause_eval_tt : 
  forall τ f, eval_cnf τ f = true <-> (forall c, In c f -> eval_clause τ c = true).
Proof.
  intros τ f. induction f as [| c cs IH].
  - split; simpl; intros; tauto.
  - rewrite eval_cons, andb_true_iff, IH.
    split; intros.
    + destruct H. intros c0 [Hinc | Hincs]. subst; auto. auto.
    + split. apply H. left. auto. intros c0 Hinc. apply H. right. auto.
Qed.


Theorem eval_ff_iff_exists_clause_eval_ff :
  forall τ f, eval_cnf τ f = false <-> (exists c, In c f /\ eval_clause τ c = false).
Proof.
  intros τ f. induction f as [| c cs IH].
  - split; simpl; intros. inversion H. destruct H as [_ [H _]]. inversion H.
  - rewrite eval_cons, andb_false_iff, IH.
    split.
    + intros [Hc | Hcs].
      * exists c. split; [left; reflexivity | assumption].
      * destruct Hcs as [c' [Hinc' Hff']]. exists c'. split; [right; assumption | assumption].
    + intros [c' [[Hsub | Hinc'] Hff]].
      * left. subst. assumption.
      * right. exists c'. auto.
Qed.


// from line 165
Definition satisfiable (f : cnf) := exists τ, eval_cnf τ f = true.

Theorem satisfiable_of_eval_tt : forall f τ, eval_cnf τ f = true -> satisfiable f.
Proof. intros f τ H. exists τ. auto. Qed.


Definition lit_var (l : literal) : V :=
  match l with | Pos v => v | Neg v => v end.

Definition clause_vars (c : clause) : list V :=
  map lit_var c.

  // from line 126 in lean
Fixpoint vars (f : cnf) : list V :=
  match f with
  | [] => []
  | c :: cs => (clause_vars c) ++ (vars cs)
  end.


Theorem mem_vars_iff_exists_mem_clause_and_mem :
  forall v f, In v (vars f) <-> (exists c, In c f /\ In v (clause_vars c)).
Proof.
  intros v f. induction f as [| c cs IH].
  - simpl. split; intros. inversion H. destruct H as [_ [H _]]. inversion H.
  - simpl. rewrite in_app_iff, IH.
    split.
    + intros [Hv | [c' [Hinc' Hv]]].
      * exists c. auto.
      * exists c'. auto.
    + intros [c' [[Hsub | Hinc'] Hv]].
      * left. subst. auto.
      * right. exists c'. auto.
Qed.


// Frome line 253 in lean
Definition eqsat (f1 f2 : cnf) := satisfiable f1 <-> satisfiable f2.


Definition agree_on (τ1 τ2 : assignment) (s : list V) :=
  forall v, In v s -> τ1 v = τ2 v.

// from line 268 in lean
Definition sequiv (f1 f2 : cnf) (s : list V) :=
  forall τ, 
    (exists σ1, eval_cnf σ1 f1 = true /\ agree_on τ σ1 s) <->
    (exists σ2, eval_cnf σ2 f2 = true /\ agree_on τ σ2 s).

End CNF_Definitions.