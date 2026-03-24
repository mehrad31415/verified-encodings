From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition assignment (V : Type) := V -> bool.

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall y, exists x, f x = y.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

Inductive literal (V : Type) : Type :=
| Pos : V -> literal V
| Neg : V -> literal V.

Arguments Pos {V} _.
Arguments Neg {V} _.

Scheme Equality for literal.

Section Literal.

Variable V : Type.

Definition var (l : literal V) : V :=
  match l with
  | Pos v => v
  | Neg v => v
  end.

Theorem var_surjective : surjective (@var V).
Proof.
  intro v.
  exists (Pos v).
  reflexivity.
Qed.

Theorem ne_of_ne_var :
  forall l1 l2 : literal V, var l1 <> var l2 -> l1 <> l2.
Proof.
  intros l1 l2 Hneq Heq.
  apply Hneq.
  now subst.
Qed.

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

Theorem flip_injective : injective flip.
Proof.
  intros l1 l2 H.
  destruct l1 as [v1 | v1], l2 as [v2 | v2]; simpl in H; inversion H; reflexivity.
Qed.

Theorem flip_inj :
  forall l1 l2 : literal V, flip l1 = flip l2 <-> l1 = l2.
Proof.
  split.
  - apply flip_injective.
  - intros ->. reflexivity.
Qed.

Theorem flip_surjective : surjective flip.
Proof.
  intro l.
  exists (flip l).
  apply flip_flip.
Qed.

Theorem flip_bijective : bijective flip.
Proof.
  split.
  - apply flip_injective.
  - apply flip_surjective.
Qed.

Theorem exists_flip_eq :
  forall l1 : literal V, exists l2 : literal V, flip l2 = l1.
Proof.
  intro l1.
  exists (flip l1).
  apply flip_flip.
Qed.

Section InteractionLemmas.

Variables l1 l2 : literal V.

Theorem var_eq_iff_eq_or_flip_eq :
  var l1 = var l2 <-> l1 = l2 \/ flip l1 = l2.
Proof.
  destruct l1 as [v1 | v1], l2 as [v2 | v2]; simpl.
  all: split; intro H.
  - left. now subst.
  - reflexivity.
  - right. now subst.
  - destruct H as [H | H]; inversion H; reflexivity.
  - right. now subst.
  - destruct H as [H | H]; inversion H; reflexivity.
  - left. now subst.
  - reflexivity.
Qed.

Theorem flip_eq_iff_eq_flip :
  flip l1 = l2 <-> l1 = flip l2.
Proof.
  destruct l1 as [v1 | v1], l2 as [v2 | v2]; simpl; split; intro H; inversion H; reflexivity.
Qed.

Theorem flip_ne_iff_ne_flip :
  flip l1 <> l2 <-> l1 <> flip l2.
Proof.
  split; intros Hneq Heq.
  - apply Hneq. now apply flip_eq_iff_eq_flip.
  - apply Hneq. now apply flip_eq_iff_eq_flip.
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

Theorem eq_of_flip_ne_of_var_eq :
  flip l1 <> l2 -> var l1 = var l2 -> l1 = l2.
Proof.
  intros Hneq Hvar.
  apply var_eq_iff_eq_or_flip_eq in Hvar.
  destruct Hvar as [Heq | Hflip].
  - exact Heq.
  - contradiction.
Qed.

End InteractionLemmas.

Theorem eval_flip :
  forall (tau : assignment V) (l : literal V),
    eval tau (flip l) = negb (eval tau l).
Proof.
  intros tau [v | v]; reflexivity.
Qed.

Theorem eval_flip2 :
  forall (tau : assignment V) (l : literal V),
    eval tau l = negb (eval tau (flip l)).
Proof.
  intros tau [v | v]; reflexivity.
Qed.

Theorem eval_flip_of_eval :
  forall (tau : assignment V) (l : literal V) (b : bool),
    eval tau l = b -> eval tau (flip l) = negb b.
Proof.
  intros tau l b H.
  rewrite eval_flip.
  now rewrite H.
Qed.

Theorem eval_of_eval_flip :
  forall (tau : assignment V) (l : literal V) (b : bool),
    eval tau (flip l) = b -> eval tau l = negb b.
Proof.
  intros tau l b H.
  rewrite eval_flip2.
  now rewrite H.
Qed.

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

Definition is_true (tau : assignment V) (l : literal V) : Prop :=
  eval tau l = true.

Definition is_false (tau : assignment V) (l : literal V) : Prop :=
  eval tau l = false.

Theorem is_pos_ne_is_neg :
  forall l : literal V, is_pos l <> is_neg l.
Proof.
  intros [v | v]; simpl; tauto.
Qed.

End Literal.

Section InhabitedPart.

Variable V : Type.
Variable defaultV : V.

Theorem is_true_ne_is_false :
  forall (tau : assignment V),
    @is_true V tau <> @is_false V tau.
Proof.
  intros tau H.
  pose (l := Pos defaultV).
  assert (H0 : is_true tau l = is_false tau l).
  { now apply (f_equal (fun f => f l)) in H. }
  unfold is_true, is_false in H0.
  unfold l in H0.
  simpl in H0.
  destruct (tau defaultV); discriminate.
Qed.

End InhabitedPart.