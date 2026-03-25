(**
Defines the properties of assignments on polymorphic variables,
including equisatisfiability and equivalence on domains.

>ean Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
Adapted into Rocq by waterloo drp group
**)


(**
For reference to self: literal.lean contains the definition of a Boolean literal.
The type of the underlying Boolean variable is polymorphic, such
that Boolean variables may be represented by nats, strings, etc.
**)

Print LoadPath. (** just for debugging idk what im doing**)



From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finset.

(**rocq analogue of
import data.finset.basic 
uses the Mathematical Components open source Rocq library (TODO download so I can test this on my own machine)**)
(*Require Import VE.cnf.Literal.*)

(**-- Represents the type of the variable stored in the literal
variables {V : Type*} **)

Require Import Coq.Init.Specif. (**provides Inhabited**)
Require Import Coq.Classes.Init.


(** 
TODO figure out how modules in rocq work
i suspect namespace assignment 
translates to smth with modules
but have little clue how to properly use them**)


(** ! # Properties **)

(*Module Type assignment_properties. (couldn't get modules to work so ignoring em for now actually)*)
    (**In Rocq, Module Types are like interfaces, where we declare things
        that are true about assignments
    Thus I put the 'Properties' section in assignment.lean here 
    And stuff implementing lemmas and such go in a later Module
    implementing everything**)
    (*apparently when using MathComp, ppl just use Sections
    not Modules*)
    

    Definition assignment (V : finType) := V -> bool.
    (**^^should be defined in literal.v**)

    (**Note with Mathematical components imported, sets of vars
    are {set V}*)

    (** Inhabited seems to be unnecessary
    equivalent is a 'default assignment'
    **)
    Definition default_assignment {V : finType} : assignment V :=
        fun _ => true.



(**
open literal
open finset // command used to make the 
   // definitions and lemmas from the Finset namespace 
   // directly accessible without needing to prefix them with Finset.

**)



Section agree_on.


    (* Declare a type of variables *)
    Variable V : finType.
    (*Rocq needs type V to be declared as a parameter in the section or as an argument in each definition.*)


    (** Since the type of assignments makes every assignment a full map, we often
    restrict the set of variables under consideration to a finite set. To
    construct assignments that extend another, we instead use a notion of
    agreement on those finite sets.
    **)

    Definition agree_on (τ₁ τ₂ : assignment V) (s : {set V}) : Prop
        := forall v, v \in s -> τ₁ v = τ₂ v.
    (**{set V} is the mathcomp analogue for finset V **)

    (** establish vars throughout this section
    Variables τ₁ τ₂ τ₃ : assignment V.
    Variables s s₁ s₂ : {set V}.
    Variables v : V.
    Variables l : literal V.*)


    (*Hint Resolve refl : core. *)(** todo look into--apparently disappears
    after section closes?**) (** the intent here is to establish this refl theorem as
    a reflexivity relation for objects in assignment V (tau agree_on's with itself)*)
    Theorem refl : forall τ : assignment V, forall s : {set V}, agree_on τ τ s.
    Proof.
        intros τ s v Hv.
        tauto.
    Qed.
    
    (**TODO figure out symm stuff**)
    Theorem symm : forall τ₁ τ₂ : assignment V, forall s : {set V}, 
        (agree_on τ₁ τ₂ s) -> (agree_on τ₂ τ₁ s).
    Proof.
        intros τ₁ τ₂ s H v Hv. (*intros generally copied from lean*)
        symmetry.
        apply H.
        assumption.
    Qed.

    Theorem comm : forall τ₁ τ₂ : assignment V, forall s : {set V}, 
        (agree_on τ₁ τ₂ s) <-> (agree_on τ₂ τ₁ s).
    Proof.
        intros τ₁ τ₂ s.
        split.
        apply symm.
        apply symm.
    Qed.

    Theorem trans : forall τ₁ τ₂ τ₃ : assignment V, forall s : {set V}, 
        (agree_on τ₁ τ₂ s) -> (agree_on τ₂ τ₃ s) -> (agree_on τ₁ τ₃ s).
    Proof.
        intros τ₁ τ₂ τ₃ s.
        intros H1 H2 v Hv.
        rewrite H1.
        rewrite H2.
        reflexivity.

        exact Hv.
        exact Hv.
    Qed.

    Theorem agree_on_nil : forall τ1 τ2 : assignment V, agree_on τ1 τ2 set0.
    Proof.
        intros τ1 τ2 v Hv.
        rewrite inE in Hv.   (* turns v \in set0 into false, 
        since smth can't be in emptyset *)
        done.
    Qed.

    Theorem agree_on_subset : forall τ1 τ2 : assignment V, forall s1 s2 : {set V},
        (forall v, v \in s1 -> v \in s2) -> agree_on τ1 τ2 s2 ->
        agree_on τ1 τ2 s1.
    Proof.
        intros τ1 τ2 s1 s2 H Hs2 v Hv.
        apply Hs2.
        apply H.
        assumption.
    Qed.
    
(*
End agree_on. (*TODO look at how Sections affect availability of Thms within*)


Section agree_on_lemmas.
    
    (* Declare a type of variables *)
    Variable V : finType.*)

    (* This doesn't work unless agree_on is in the same section*)
    

    (*says that equality of V is decidable*)
    Hypothesis decidable_eq : forall x y : V, 
        {x = y} + {x <> y}.


    (*if two assignments agree on a set of variables
    and they also agree on a specific variable v,
    then they agree on the union of that variable and the set*)


    Theorem agree_on_union_of_agree_on_of_eq : 
        forall τ₁ τ₂ : assignment V, forall s : {set V}, forall v : V,
        (agree_on τ₁ τ₂ s) -> τ₁ v = τ₂ v -> 
        (agree_on τ₁ τ₂ ([set v] :|: s)). (** in mathcomp, :|: is notation for set union*)
    Proof.
        intros τ1 τ2 s v Hagree Heq u Hu.
        rewrite inE in Hu. (* split into cases*)
        (* destruct Hu as [Hu1 | Hu2]. Can't use this b/c \in is a bool, not a Prop*)
        case/orP: Hu => Hcase.
        
        - move/eqP: Hcase.      (* u = v *)
          intros uEqv.
          rewrite inE in uEqv. (*gives (u == v) == true*)
          (* TODO CAN DEF IMPROVE THIS*)

          assert ((u == v) = true ) as hh.
          {
            move/eqP in uEqv.
            exact.
          }


          assert ((u == v) = true -> u = v).
          {  
            intros H.
            move/eqP: H => <-.
            reflexivity.
          }

          assert (u=v).
          {
            apply H.
            exact hh.
          }
          (*FINALLY managed to make u = v*)
          rewrite H0.
          exact Heq.
        - apply Hagree.
          exact Hcase.
    Qed.

    
    Theorem agree_on_union :  forall τ1 τ2 : assignment V,
        forall s1 s2 : {set V},  (agree_on  τ1 τ2 s1) -> (agree_on  τ1 τ2 s2) 
        -> (agree_on  τ1 τ2 (s1 :|: s2)).
    Proof.
        intros τ1 τ2 s1 s2 H1 H2 v Hv.
        rewrite inE in Hv.
        case/orP: Hv => Hcase. 
        - apply H1.
          exact Hcase.
        - apply H2.
          exact Hcase.
    Qed.

    Theorem agree_on_inter : forall τ₁ τ₂ : assignment V,
        forall s₁ s₂ : {set V}, (agree_on τ₁ τ₂ s₁) ->
        (agree_on τ₁ τ₂ s₂) -> (agree_on τ₁ τ₂ (s₁ :&: s₂)). (*:&: is set intersection*)
    Proof.
        intros τ1 τ2 s1 s2 H1 H2 v Hv.
        rewrite inE in Hv.
        apply H1.
        move/andP: Hv => [Hv1 Hv2].
        exact Hv1. 
    Qed.

    
    Theorem agree_on_union_left: forall τ₁ τ₂ : assignment V,
        forall s₁ s₂ : {set V}, (agree_on τ₁ τ₂ (s₁ :|: s₂)) ->(agree_on τ₁ τ₂ s₁). 
    Proof.
        intros τ1 τ2 s1 s2 H v Hv.
        apply H.
        rewrite inE.
        rewrite Hv.
        simpl.
        done.
    Qed.

    
    Theorem agree_on_union_right: forall τ₁ τ₂ : assignment V,
        forall s₁ s₂ : {set V}, (agree_on τ₁ τ₂ (s₁ :|: s₂)) ->(agree_on τ₁ τ₂ s₂). 
    Proof.
        intros τ1 τ2 s1 s2 H v Hv.
        apply H.
        rewrite inE.
        rewrite Hv.
        rewrite orbT. (*if one of bools in an or is true, they all true*)
        done.
    Qed.

(*End agree_on_lemmas. 
*)


(* TODO get literal implementation *)





Theorem eval_eq_of_agree_on_of_var_mem : forall τ1 τ2 : assignment V,
    forall s : {set V}, forall l : literal, 
      agree_on τ1 τ2 s ->
      s (var l) ->
      eval l τ1 = eval l τ2.

Theorem eval_eq_of_agree_on_of_var_mem : forall τ₁ τ₂ : assignment V,
    forall s : {set V}, forall l : literal V, 
      agree_on τ1 τ2 s ->
      s (var l) ->
      eval l τ1 = eval l τ2.

    (agree_on τ₁ τ₂ s) -> l.var \in s -> l.eval τ₁ = l.eval τ₂.
Proof.
    intros τ1 τ2 s l.

Qed.


theorem eval_eq_of_agree_on_of_var_mem : (agree_on τ₁ τ₂ s) → l.var ∈ s → l.eval τ₁ = l.eval τ₂ :=
assume h₁ h₂, by { cases l, exact h₁ l h₂, exact congr_arg bnot (h₁ l h₂) }







End agree_on.
