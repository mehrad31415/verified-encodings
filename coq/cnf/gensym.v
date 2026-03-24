// gensym aims to generate fresh variables for the CNF encodings
// uses proofs for freshness of variable generation

Require Import cnf.cnf
Require Import data.list.basic
Require Import data.set.basic

Section Gensym.

Import ListNotations
Variable A : Type.

(* gensym is a struct/object
 offset is the current position on a natural number numberline
 f conversts natural number into variable a
 f_inj guarantees unique variables, ie. two different numbers can never produce the same variable 
A gensym object only tracks a position along the natural number
   line. 
offset is set to this natural number
When provided with an injective function (f_inj) from the naturals to the
boolean variable type, the gensym will provably generate fresh variables,
with respect to those variables already generated.
offset works like a counter
the function f converts numbers into variables 
makes sure that different numbers always produce different numbers; ensures uniqueness
everytime you move the counter forward, you get a new unique variable *)


Record gensym := {
	offset : nat;
	f : nat -> A
	f_inj : forall x y, f x = f y -> x = y
}.


Variable f0 : nat -> A.
Hypothesis f0_inj : forall x y, f0 x = f0 y -> x = y.

(*Initial Gensym that starts at 0*)

Definition init : gensym := 
	{| offset := 0;
	   f := 0;
	   f_inj := f0_inj |}

(* aim: create a gensym that never produces a variable within a list
finds maximum of list and starts offset at max + 1 *)

Variable fi : A -> nat.
Hypothesis fi_inj : forall x y, fi x = fi y -> x = y.
Hypothesis rinv : forall x, f0 (fi x) = x.


(* Fixpoint definition for a recursive function *)

Fixpoint max_in_list (l : list nat) : nat := 
	match l with
	| [] => 0 (* for an empty list *)
	| x :: xs => max x (max_list xs)
	end. 

Definition seed (l : list A) : gensym := 
	match l with
	| [] => init
	| _ =>
		{| offset := 1 + max_in_list (map fi l) :
		   f := f0
		   f_inj := f0_inj |}
	end.

(* Fresh variable generation *)

(* Generate a single fresh variable and update gensym *)

Definition fresh (g : gensym) : A * gensym := 
    let new_var := g.(f) (g.(offset)) in
    let new_gensym := {| offset := 1 + g.(offset); 
                        f := g.(f); 
                        f_inj := g.(f_inj) |} in
    (new_var, new_gensym).


(* If you generate a fresh variable using fresh g, the returned gensym has its offset incremented by 1 *)
Lemma fresh_offset (g : gensym) : 
    snd (fresh g).(offset) = 1 + g.(offset).
Proof. destruct (fresh g) as [new_var new_gensym]. simpl. reflexivity. Qed.

(* Generating a fresh variable does not change the function f in gensym *)
Lemma fresh_f (g: gensym) :
    snd (fresh g).(f) = g.(f).
Proof. destruct (fresh g); simpl. reflexivity. Qed.

(* The variable returned by fresh is exactly g.f g.offset*)
Lemma fresh_var (g: gensym) :
    fst (fresh g) = g.(f) (g.(offset)).
Proof. reflexivity. Qed.

(* The function f in the updated gensym is still injective *)
Lemma fresh_f_inj (g: gensym) :
    forall x y, (snd (fresh g)).(f) x = (snd (fresh g)).(f) y -> x = y.
Proof. unfold fresh; simple; auto. Qed.

(* Generate multiple fresh variables and update gensym *)

Fixpoint nfresh (g : gensym) (n : nat) : list A * gensym := 
    match n with
    | 0 => ([], g)
    | S n' => 
        let (new_var, new_gensym) := fresh g in
        let (rest_vars, final_gensym) := nfresh new_gensym n' in
        (new_var :: rest_vars, final_gensym)
    end.

(* Length of generated list equals n *)
Lemma nfresh_length (g : gensym) (n : nat) :
    length (fst (nfresh g n)) = n.
Proof. 
    induction n; simpl; auto. 
    destruct (fresh g); destruct (nfresh {| offset := 1 + offset0; f := f0; f_inj := f0_inj |} n); simpl; auto.

(* Stock: set of variables the gensym could create *)
Definition stock (g : gensym) : Ensemble A := 
    fun x => exists n, g.(f) (g.(offset) + n) = x.

(* Every fresh variable is in the stock *)
Lemma fresh_in_stock (g : gensym) :
    let (new_var, new_gensym) := fresh g in
    In _ (stock g) new_var.
Proof. unfold fresh, stock; simpl. exists 0. reflexivity. Qed.

(* #nth variable *)

Definition nth (g : gensym) (n : nat) : A := 
    g.(f) (g.(offset) + n).

(* Different indicies produce different variables *)
Lemma nth_ne_of_ne (g : gensym) i  j :
    i <> j -> nth g i <> nth g j.
Proof. 
    intros Hneq.
    unfold nth.
    apply g.(f_inj).
    apply Nat.add_cancel_r.
Qed.

(* The 0th variable equals fresh *)
Lemma nth_0_fresh (g : gensym) :
    nth g 0 = fst (fresh g).
Proof. unfold nth, fresh; simpl; lia. Qed.

(* Every nth variable is in the stock *)
Lemma nth_in_stock (g : gensym) (n : nat) :
    In _ (stock g) (nth g n).

Proof. unfold nth, stock; simpl; exists n; lia. Qed.

End Gensym.