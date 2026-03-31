(* Explode.v — Powerset clause enumeration
   Phase 2 (DRP Winter 2026)
   Based on src/parity/explode.lean by Codel, Avigad, Heule (CMU) *)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Import ListNotations.

From VE Require Import cnf.Literal.
From VE Require Import cnf.Clause.
From VE Require Import cnf.Cnf.

Set Implicit Arguments.

Section ExplodeDefs.

Variable V : Type.

(* Produce all possible polarity assignments on a list of variables.
   For n variables, produces 2^n clauses. *)
Fixpoint explode (vars : list V) : list (clause V) :=
  match vars with
  | [] => [[]]
  | v :: vs =>
    map (cons (Pos v)) (explode vs) ++ map (cons (Neg v)) (explode vs)
  end.

Theorem explode_nil : explode ([] : list V) = [[]].
Proof. reflexivity. Qed.

Theorem explode_singleton : forall (v : V),
  explode [v] = [[Pos v]; [Neg v]].
Proof. reflexivity. Qed.

Theorem length_explode : forall (l : list V),
  length (explode l) = 2 ^ (length l).
Proof.
  induction l as [| v vs IH].
  - reflexivity.
  - change (explode (v :: vs)) with
      (map (cons (Pos v)) (explode vs) ++ map (cons (Neg v)) (explode vs)).
    rewrite length_app.
    assert (H1 : length (map (cons (Pos v)) (explode vs)) = length (explode vs)).
    { apply length_map. }
    assert (H2 : length (map (cons (Neg v)) (explode vs)) = length (explode vs)).
    { apply length_map. }
    rewrite H1, H2, IH. simpl. lia.
Qed.

Theorem length_eq_of_mem_explode : forall (l : list V) (c : clause V),
  In c (explode l) -> length c = length l.
Proof.
  induction l as [| v vs IH]; intros c Hc.
  - simpl in Hc. destruct Hc as [Hc | Hc]; [subst; reflexivity | contradiction].
  - simpl in Hc. apply in_app_iff in Hc. destruct Hc as [Hc | Hc];
    apply in_map_iff in Hc; destruct Hc as [c' [Hc' Hin]]; subst;
    simpl; f_equal; apply IH; exact Hin.
Qed.

(* Every clause in explode has the same variables as the input list *)
Theorem map_var_eq_of_mem_explode : forall (l : list V) (c : clause V),
  In c (explode l) -> map (var (V:=V)) c = l.
Proof.
  induction l as [| v vs IH]; intros c Hc.
  - simpl in Hc. destruct Hc as [Hc | Hc]; [subst; reflexivity | contradiction].
  - simpl in Hc. apply in_app_iff in Hc. destruct Hc as [Hc | Hc];
    apply in_map_iff in Hc; destruct Hc as [c' [Hc' Hin]]; subst;
    simpl; f_equal; apply IH; exact Hin.
Qed.

End ExplodeDefs.
