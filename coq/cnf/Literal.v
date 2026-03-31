(* Literal.v — Boolean literals for SAT encodings
   Original Coq implementation by Jeannie (Phase 1, DRP Winter 2026)
   Based on src/cnf/literal.lean by Codel, Avigad, Heule (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Assignments give boolean values to variables *)
Definition assignment (V : Type) := V -> bool.

(* A literal is a positive or negative occurrence of a variable *)
Inductive literal (V : Type) : Type :=
| Pos : V -> literal V
| Neg : V -> literal V.

Arguments Pos {V} _.
Arguments Neg {V} _.

Section Literal.

Variable V : Type.

(* Extract the underlying variable *)
Definition var (l : literal V) : V :=
  match l with
  | Pos v => v
  | Neg v => v
  end.

Definition eval (tau : assignment V) (l : literal V) : bool :=
  match l with
  | Pos v => tau v
  | Neg v => negb (tau v)
  end.

Definition flip (l : literal V) : literal V :=
  match l with
  | Pos v => Neg v
  | Neg v => Pos v
  end.

(* Flip properties *)

Theorem flip_ne :
  forall l : literal V, flip l <> l.
Proof.
  intros [v | v]; discriminate.
Qed.

Theorem flip_flip :
  forall l : literal V, flip (flip l) = l.
Proof.
  intros [v | v]; reflexivity.
Qed.

Theorem flip_var_eq :
  forall l : literal V, var (flip l) = var l.
Proof.
  intros [v | v]; reflexivity.
Qed.

Theorem flip_injective :
  forall l1 l2 : literal V, flip l1 = flip l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  destruct l1 as [v1 | v1], l2 as [v2 | v2];
    simpl in H; inversion H; reflexivity.
Qed.

Theorem flip_inj :
  forall l1 l2 : literal V, flip l1 = flip l2 <-> l1 = l2.
Proof.
  split.
  - apply flip_injective.
  - intros ->. reflexivity.
Qed.

Theorem flip_surjective :
  forall l : literal V, exists l2, flip l2 = l.
Proof.
  intro l. exists (flip l). apply flip_flip.
Qed.

(* Var and flip interaction *)

Section InteractionLemmas.

Variables l1 l2 : literal V.

Theorem var_eq_iff_eq_or_flip_eq :
  var l1 = var l2 <-> l1 = l2 \/ flip l1 = l2.
Proof.
  destruct l1 as [v1 | v1], l2 as [v2 | v2]; simpl; split; intro H.
  - left. f_equal. exact H.
  - destruct H as [H | H]; inversion H; reflexivity.
  - right. f_equal. exact H.
  - destruct H as [H | H]; inversion H; reflexivity.
  - right. f_equal. exact H.
  - destruct H as [H | H]; inversion H; reflexivity.
  - left. f_equal. exact H.
  - destruct H as [H | H]; inversion H; reflexivity.
Qed.

Theorem flip_eq_iff_eq_flip :
  flip l1 = l2 <-> l1 = flip l2.
Proof.
  destruct l1 as [v1 | v1], l2 as [v2 | v2]; simpl;
    split; intro H; inversion H; reflexivity.
Qed.

Theorem flip_eq_of_ne_of_var_eq :
  l1 <> l2 -> var l1 = var l2 -> flip l1 = l2.
Proof.
  intros Hneq Hvar.
  apply var_eq_iff_eq_or_flip_eq in Hvar.
  destruct Hvar as [Heq | Hflip].
  - contradiction.
  - exact Hflip.
Qed.

End InteractionLemmas.

(* Flip evaluation *)

Theorem eval_flip :
  forall (tau : assignment V) (l : literal V),
    eval tau (flip l) = negb (eval tau l).
Proof.
  intros tau [v | v]; simpl.
  - reflexivity.
  - rewrite negb_involutive. reflexivity.
Qed.

Theorem eval_flip2 :
  forall (tau : assignment V) (l : literal V),
    eval tau l = negb (eval tau (flip l)).
Proof.
  intros tau l. rewrite eval_flip. rewrite negb_involutive. reflexivity.
Qed.

Theorem eval_flip_of_eval :
  forall (tau : assignment V) (l : literal V) (b : bool),
    eval tau l = b -> eval tau (flip l) = negb b.
Proof.
  intros tau l b H. rewrite eval_flip. now rewrite H.
Qed.

Theorem eval_of_eval_flip :
  forall (tau : assignment V) (l : literal V) (b : bool),
    eval tau (flip l) = b -> eval tau l = negb b.
Proof.
  intros tau l b H. rewrite eval_flip2. now rewrite H.
Qed.

(* Positives and negatives *)

Definition is_pos (l : literal V) : Prop :=
  match l with
  | Pos _ => True
  | Neg _ => False
  end.

Definition is_neg (l : literal V) : Prop :=
  match l with
  | Pos _ => False
  | Neg _ => True
  end.

End Literal.
