(* Encoding.v — Encoding correctness and well-behavedness
   Original Coq implementation by Sarah (Phase 1, DRP Winter 2026)
   Rewritten for compilation; kept correctness/well-behavedness concepts.
   Based on src/cnf/encoding.lean by Codel, Avigad, Heule (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From VE Require Import cnf.Literal.
From VE Require Import cnf.Assignment.
From VE Require Import cnf.Clause.
From VE Require Import cnf.Cnf.
From VE Require Import cnf.Gensym.

Set Implicit Arguments.

Section EncodingDefs.

Variable V : Type.

(* A constraint is a function from a list of booleans to a boolean *)
Definition constraint := list bool -> bool.

(* An encoding function takes literals and a gensym, produces a CNF and updated gensym *)
Definition enc_fn := list (literal V) -> gensym V -> cnf V * gensym V.

(* Disjointness: no variable in the literal list is in the gensym's stock *)
Definition disj (l : list (literal V)) (g : gensym V) : Prop :=
  forall v, In v (clause_vars l) -> ~ stock g v.

(* Evaluate a constraint on a list of literals under an assignment *)
Definition constraint_eval (c : constraint) (tau : assignment V) (l : list (literal V)) : bool :=
  c (map (eval tau) l).

(* A CNF formula encodes a constraint on input literals:
   The constraint is true iff there exists an extending assignment
   that satisfies the CNF and agrees on the input variables. *)
Definition formula_encodes (c : constraint) (F : cnf V) (l : list (literal V)) : Prop :=
  forall tau,
    constraint_eval c tau l = true <->
    exists sigma, eval_cnf sigma F = true /\ agree_on tau sigma (clause_vars l).

(* An encoding function is correct if it always produces a correct formula *)
Definition is_correct (c : constraint) (enc : enc_fn) : Prop :=
  forall (l : list (literal V)) (g : gensym V),
    disj l g ->
    formula_encodes c (fst (enc l g)) l.

(* An encoding is well-behaved if it only uses input and gensym variables *)
Definition is_wb (enc : enc_fn) : Prop :=
  forall (l : list (literal V)) (g : gensym V),
    disj l g ->
    (* The updated gensym's stock is a subset of the original *)
    (forall a, stock (snd (enc l g)) a -> stock g a) /\
    (* All variables in the output CNF are from inputs or original stock *)
    (forall v, In v (cnf_vars (fst (enc l g))) ->
               In v (clause_vars l) \/ stock g v).

(* Combined: an encoding function encodes a constraint correctly and well-behavedly *)
Definition encodes (c : constraint) (enc : enc_fn) : Prop :=
  is_correct c enc /\ is_wb enc.

(* Constraint append: conjunction of two constraints *)
Definition constraint_append (c1 c2 : constraint) : constraint :=
  fun l => c1 l && c2 l.

(* Identity constraint *)
Definition constraint_id : constraint := fun _ => true.

Theorem constraint_id_left : forall c : constraint,
  (fun l => constraint_id l && c l) = c.
Proof.
  intro c. apply functional_extensionality.
  intro l. simpl. reflexivity.
Qed.

(* Direct encoding: no fresh variables needed *)
Definition dir_enc (f : list (literal V) -> cnf V) : enc_fn :=
  fun l g => (f l, g).

(* Identity encoding *)
Definition enc_id : enc_fn := fun l g => ([], g).

Theorem enc_id_is_wb : is_wb enc_id.
Proof.
  intros l g Hdisj. split.
  - intros a Ha. exact Ha.
  - intros v Hv. simpl in Hv. contradiction.
Qed.

(* Encoding function append *)
Definition enc_append (enc1 enc2 : enc_fn) : enc_fn :=
  fun l g =>
    let (F1, g1) := enc1 l g in
    let (F2, g2) := enc2 l g1 in
    (F1 ++ F2, g2).

(* Fold over a list of encoding functions *)
Definition enc_fold (encs : list enc_fn) : enc_fn :=
  fold_right enc_append enc_id encs.

End EncodingDefs.

