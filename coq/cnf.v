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
Definition cnf := list (clause V). 
 

Hypothesis V_eq_dec : forall x y : V, {x = y} + {x <> y}.


Definition assignment := V -> bool.



Definition eval_literal (τ : assignment) (l : literal V) : bool :=
  match l with
  | Pos v => τ v
  | Neg v => negb (τ v)
  end.

Definition eval_clause (τ : assignment) (c : clause V) : bool :=
  existsb (eval_literal τ) c.


(*starting from protected def from line 68
Evaluate a CNF formula under a given assignment.
c1 AND c2 AND c3 if any clause is false, then the whole is false.*)
Definition eval_cnf (τ : assignment) (f : cnf) : bool :=
  fold_right (fun c b => b && (eval_clause τ c)) true f.



Theorem eval_nil : forall τ, eval_cnf τ [] = true.
Proof. reflexivity. Qed.

Theorem eval_singleton : forall τ c, eval_cnf τ [c] = eval_clause τ c.
Proof. intros. simpl. rewrite andb_true_r. reflexivity. Qed.

Theorem eval_cons : forall τ c f, eval_cnf τ (c :: f) = eval_clause τ c && eval_cnf τ f.
Proof. intros. simpl. rewrite andb_comm. reflexivity. Qed.


(*from line 79 
cnf is true iff all clauses are true.*)
Theorem eval_tt_iff_forall_clause_eval_tt : 
  forall τ f, eval_cnf τ f = true <-> (forall c, In c f -> eval_clause τ c = true).
Proof.
  intros τ f. induction f as [| c cs IH].
  - split; simpl; intros; try contradiction; auto.
  - simpl. rewrite andb_true_iff, IH.
    split; intros.
    + destruct H as [Hc Hcs].
      intros c0 [H | H].
      * subst. assumption.
      * apply Hcs. assumption.
    + split.
      * apply H. left. reflexivity.
      * intros c0 Hc0. apply H. right. assumption.
Qed.

(*cnf is false iff there exists a clause that is false.*)
Theorem eval_ff_iff_exists_clause_eval_ff :
  forall τ f, eval_cnf τ f = false <-> (exists c, In c f /\ eval_clause τ c = false).
Proof.
  intros τ f. induction f as [| c cs IH].
  - split; simpl; intros.
    + discriminate.
    + destruct H as [c [H _]]. inversion H.
  - simpl. rewrite andb_false_iff, IH.
    split.
    + intros [Hc | Hcs].
      * exists c. split; [left; reflexivity | assumption].
      * destruct Hcs as [c' [Hinc' Hff']].
        exists c'. split; [right; assumption | assumption].
    + intros [c' [[H | H] Hff]].
      * subst. left. assumption.
      * right. exists c'. split; assumption.
Qed.



(*from line 165
if there exists an assignment that makes the CNF true, then it is satisfiable.*)
Definition satisfiable (f : cnf) := exists τ, eval_cnf τ f = true.

Theorem satisfiable_of_eval_tt : forall f τ, eval_cnf τ f = true -> satisfiable f.
Proof. intros f τ H. exists τ. auto. Qed.


Definition lit_var (l : literal V) : V :=
  match l with | Pos v => v | Neg v => v end.

Definition clause_vars (c : clause V) : list V :=
  map lit_var c.

(*from line 126 in lean
count the number of clauses that are true/false*)
Definition count_tt (τ : assignment) (f : cnf) : nat :=
  length (filter (fun c => eval_clause τ c) f).
Definition count_ff (τ : assignment) (f : cnf) : nat :=
  length (filter (fun c => negb (eval_clause τ c)) f).

(* # clauses that are true + # clauses that are false = #clauses*)
Theorem count_tt_nil :
  forall τ, count_tt τ [] = 0.
Proof. intros; reflexivity. Qed.

(*clauses that are false + clauses that are true = total clauses*)
Theorem count_ff_nil :
  forall τ, count_ff τ [] = 0.
Proof. intros; reflexivity. Qed.

(* count the number of clauses that are true in a cnf formula. *)
Theorem count_tt_cons :
  forall τ c f,
  count_tt τ (c :: f) =
    (if eval_clause τ c then 1 else 0) + count_tt τ f.
Proof.
  intros τ c f. unfold count_tt. simpl.
  destruct (eval_clause τ c); simpl; lia.
Qed.

(* count the number of clauses that are false in a cnf formula. *)
Theorem count_tt_app :
  forall τ f1 f2,
  count_tt τ (f1 ++ f2) = count_tt τ f1 + count_tt τ f2.
Proof.
  intros τ f1 f2.
  unfold count_tt.
  rewrite filter_app.
  rewrite app_length.
  reflexivity.
Qed.

(*
 Collect all variables that appear in a CNF formula.*) 
Fixpoint vars (f : cnf) : list V :=
  match f with
  | [] => []
  | c :: cs => (clause_vars c) ++ (vars cs)
  end.


Theorem mem_vars_iff_exists_mem_clause_and_mem :
  forall v f, In v (vars f) <-> (exists c, In c f /\ In v (clause_vars c)).
Proof.
  intros v f. induction f as [| c cs IH].
  - simpl. split; intros.
    + contradiction.
    + destruct H as [c [H _]]. inversion H.
  - simpl. rewrite in_app_iff, IH.
    split.
    + intros [Hv | [c' [Hinc' Hv]]].
      * exists c. split; [left; reflexivity | assumption].
      * exists c'. split; [right; assumption | assumption].
    + intros [c' [[H | H] Hv]].
      * subst. left. assumption.
      * right. exists c'. split; assumption.
Qed.

(*vars_append*)
Theorem vars_append :
  forall f1 f2,
  vars (f1 ++ f2) = vars f1 ++ vars f2.
Proof.
  induction f1 as [| c cs IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(*caluse vars subset*)
Theorem clause_vars_subset :
  forall c f,
  In c f ->
  forall v, In v (clause_vars c) -> In v (vars f).
Proof.
  intros c f H.
  induction f as [| c' cs IH].
  - inversion H.
  - simpl. intros v Hv.
    destruct H.
    + subst. apply in_or_app. left. assumption.
    + apply in_or_app. right.
      apply IH; assumption.
Qed.

(*vars subset*)
Theorem vars_subset_of_subset :
  forall f1 f2,
  subset_cnf f1 f2 ->
  forall v, In v (vars f1) -> In v (vars f2).
Proof.
  intros f1 f2 Hsub v Hv.
  apply mem_vars_iff_exists_mem_clause_and_mem in Hv.
  destruct Hv as [c [Hc Hv]].
  apply mem_vars_iff_exists_mem_clause_and_mem.
  exists c.
  split.
  - apply Hsub. assumption.
  - assumption.
Qed.


(*Frome line 253 in lean
2 cnf are equivalent iff they have the same satisfiability.*)
Definition eqsat (f1 f2 : cnf) := satisfiable f1 <-> satisfiable f2.


Definition agree_on (τ1 τ2 : assignment) (s : list V) :=
  forall v, In v s -> τ1 v = τ2 v.


(*from line 268 in lean
2 cnf are equivalent on a set of variables iff for any assignment, 
there exists an assignment that agrees on the set of variables and makes the cnf true.*)
Definition sequiv (f1 f2 : cnf) (s : list V) :=
  forall τ, 
    (exists σ1, eval_cnf σ1 f1 = true /\ agree_on τ σ1 s) <->
    (exists σ2, eval_cnf σ2 f2 = true /\ agree_on τ σ2 s).

(* 2 cnf are equivalent iff for any assignment, there exists an assignment 
that agrees on the variables and makes the cnf true.*)
Theorem eval_eq_of_agree_on :
  forall τ1 τ2 f,
  agree_on τ1 τ2 (vars f) ->
  eval_cnf τ1 f = eval_cnf τ2 f.
Proof.
  intros τ1 τ2 f H.
  induction f as [| c cs IH].
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    2:{
      intros v Hv.
      apply H.
      simpl. apply in_or_app. right. assumption.
    }
Abort.
End CNF_Definition.