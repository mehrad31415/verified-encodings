(**
Defines the properties of assignments on polymorphic variables,
including equisatisfiability and equivalence on domains.

>ean Authors: Cayden Codel, Jeremy Avigad, Marijn Heule
Carnegie Mellon University
Adapted into Rocq by Waterloo DRP group
**)


(**
For reference to self: literal.lean contains the definition of a Boolean literal.
The type of the underlying Boolean variable is polymorphic, such
that Boolean variables may be represented by nats, strings, etc.
**)

Print LoadPath. (** just for debugging**)



From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finset.
Require Import Classical.
From Coq Require Import Logic.FunctionalExtensionality.

(**rocq analogue of
import data.finset.basic 
uses the Mathematical Components open source Rocq library**)
Require Import VE.cnf.Literal.

(**-- Represents the type of the variable stored in the literal
variables {V : Type*} **)

Require Import Coq.Init.Specif. (**provides Inhabited**)
Require Import Coq.Classes.Init.



(** ! # Properties **)

(*Module Type assignment_properties. (couldn't get modules to work so ignoring em for now actually)*)
    (**In Rocq, Module Types are like interfaces, where we declare things
        that are true about assignments
    Thus I put the 'Properties' section in assignment.lean here 
    And stuff implementing lemmas and such go in a later Module
    implementing everything**)
    (*apparently when using MathComp, ppl just use Sections
    not Modules*)
    

    (*Definition assignment (V : finType) := V -> bool.
    (**^^should be defined in literal.v, is just for temp usage**)*)

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



(* If there's 2 assignments agreeing on a set of vars, and there
is a literal in that set, then they agree on that literal*)
Theorem eval_eq_of_agree_on_of_var_mem : forall τ1 τ2 : assignment V,
    forall s : {set V}, forall l : literal V, 
        (agree_on τ1 τ2 s) -> (var l) \in s
        -> eval τ1 l = eval τ2 l.
Proof.
    intros τ1 τ2 s l H1 H2.
    unfold eval.
    destruct l as [v | v]. (*destruct pattern match on l's cases*)
  - (* l is Pos case *)
    apply H1.
    exact H2.
  - (* l is Neg case *)
    rewrite (H1 v H2). (* uses agree_on τ1 τ2 s to replace tau1 and tau2 *)
    reflexivity.
Qed.


(* Extending an assignment τ1 to assignment τ2 which is the same
everywhere except possibly at v, where it becomes a given bool b
 *)
Theorem exists_agree_on_and_eq_of_not_mem :
    forall (τ1 : assignment V) (b : bool) (v : V) (s : {set V}),
    v \notin s -> exists τ2, agree_on τ1 τ2 s /\ τ2 v = b.
Proof.
  intros τ1 b v s HvNotin.
  
  (* define τ2 *)
  exists (fun x : V => if x == v then b else τ1 x).

  split.
  - (* showing agree_on of τ1 and our defined τ2 *)
    intros x.
    intros Hx.

    assert (x != v) as Hneq.
    {
        apply/negP.
        intro Heq.
        move/eqP in Heq.
        rewrite Heq in Hx.
        move/negP: HvNotin => /(_ Hx). (*contradiction*)
        tauto.
    }

    (* simplify the if *)
    rewrite (negbTE Hneq).
    reflexivity.

  - (* τ2 v = b *)
    rewrite /=.
    rewrite eqxx.
    reflexivity.
Qed.


(* Given assignments tau1, f on disjoint sets s1, s2, respectively,
there exists an assignment tau2 made up of tau1 and tau2
with tau2 agreeing on each of them on each of their respective
sets.
In other words, extends tau1 assignment by an assignment f
to a new assignment tau2.*)
Theorem exists_agree_on_and_eq_of_disjoint :
    forall (τ1 τ2 f : assignment V) (v : V) (s1 s2 : {set V}),
    [disjoint s1 & s2] -> exists τ2, (agree_on τ1 τ2 s1) /\ 
    (forall v, v \in s2 -> τ2 v = f v).
Proof.
    (*Search disjoint.*)
    intros τ1 τ2 f v s1 s2 H.
    exists (fun x => if x \in s2 then f x else τ1 x).

    split.
    - intros vv Hvv.
      assert (Hnotin : vv \in s2 = false).
      {
        (* given disjoint sets s1 & s2 and v in left set, 
        give non-membership in the right set *)
        (*pose proof (disjointFr).*)
        pose proof (disjointFr H Hvv). (* just use the right lemma basically lol*)
        exact H0.
      }
      rewrite Hnotin.
      reflexivity.

    - intros vv Hvv.
      rewrite Hvv.
      reflexivity.
Qed.



(* ! aite *)
(*assignment if-then-else*)


(* Defines a useful pattern we will see over and over again:
a new assignment that uses tau1 if the variable is in a set,
and uses tau2 otherwise*)
Definition aite (s : {set V}) (τ1 τ2 : assignment V) 
    : assignment V :=
    (fun v => if v \in s then τ1 v else τ2 v).


Theorem aite_nil : forall (τ1 τ2 : assignment V),
    (aite set0 τ1 τ2) = τ2.
Proof.
    (*use functional extensionality: i.e., unfold to show 
    both sides give the same value on every possible input v*)
    intros τ1 τ2.
    rewrite /aite.
    apply functional_extensionality => v.
    rewrite inE.
    reflexivity.
Qed.


Theorem aite_pos : forall (s : {set V}) (v : V) (τ1 τ2 : assignment V),
    v \in s -> (aite s τ1 τ2) v = τ1 v.
Proof.
    intros s v τ1 τ2 H.
    rewrite /aite.
    rewrite H.
    reflexivity.
Qed.


Theorem aite_neg : forall (s : {set V}) (v : V) (τ1 τ2 : assignment V),
    v \notin s -> (aite s τ1 τ2) v = τ2 v.
Proof.
    intros s v τ1 τ2 H.

    rewrite /aite.
    pose proof (negbTE H). (* converts notin into false of in *)
    rewrite H0. 
    reflexivity.
Qed.


Theorem aite_pos_lit : forall (s : {set V}) (l : literal V)
    (τ1 τ2 : assignment V), (var l) \in s ->
    eval (aite s τ1 τ2) l = eval τ1 l.
Proof.
    intros s l τ1 τ2 H.
    unfold eval.
    destruct l as [v | v]. (*destruct pattern match on l's cases*)

    - rewrite aite_pos.
      reflexivity.
      rewrite H.
      trivial.

    - rewrite aite_pos.
      reflexivity.
      rewrite H.
      trivial.
Qed.


Theorem aite_neg_lit : forall (s : {set V}) (l : literal V)
    (τ1 τ2 : assignment V), (var l) \notin s ->
    eval (aite s τ1 τ2) l = eval τ2 l.
Proof.
    intros s l τ1 τ2 H.
    unfold eval.
    destruct l as [v | v]. (*destruct pattern match on l's cases*)

    - rewrite aite_neg.
      reflexivity.
      rewrite H.
      trivial.

    - rewrite aite_neg.
      reflexivity.
      rewrite H.
      trivial.
Qed.


Theorem aite_agree_on : forall (s : {set V}) 
    (τ1 τ2 : assignment V), 
    agree_on (aite s τ1 τ2) τ1 s.
Proof.
    intros s τ1 τ2 v Hv.
    
    rewrite aite_pos.
    reflexivity.
    
    rewrite Hv.
    trivial.
Qed.


Theorem aite_agree_on_of_disjoint : forall (τ1 τ2 : assignment V)
    (s1 s2 : {set V}), 
    [disjoint s1 & s2] -> (agree_on τ2 (aite s1 τ1 τ2) s2).
Proof.
    intros τ1 τ2 s1 s2 H v Hv.

    rewrite aite_neg.
    reflexivity.

    (* given disjoint sets s1 & s2 and v in right set, 
    give non-membership in the left set *)
    pose proof (disjointFl H Hv).

    rewrite H0.
    trivial.
Qed.


Theorem aite_agree_on_of_subset : forall (τ1 τ2 : assignment V)
    (s1 s2 : {set V}), 
    s2 \subset s1 -> agree_on τ1 (aite s1 τ1 τ2) s2.
Proof.
    intros τ1 τ2 s1 s2 H v Hv.

    rewrite aite_pos.
    reflexivity.

    (* unfold subset relationship *)
    move/subsetP in H.
    pose proof (H v Hv).
    exact H0.
Qed.


Theorem aite_agree_on_of_agree_on_of_agree_on : 
    forall (s : {set V}) (τ sig1 sig2 : assignment V), 
    agree_on τ sig1 s -> agree_on τ sig2 s -> 
    forall (t : {set V}), agree_on τ (aite t sig1 sig2) s.
Proof.
    intros s τ sig1 sig2 H1 H2 t v Hv.
    rewrite/aite.
    case (v \in t).
    - pose proof (H1 v Hv).
      exact H.
    - pose proof (H2 v Hv).
      exact H.
Qed.


Theorem aite_eq_second_of_agree_on : 
    forall (τ1 τ2 : assignment V)  (s : {set V}), 
    agree_on τ1 τ2 s -> aite s τ1 τ2 = τ2.
Proof.
    intros τ1 τ2 s H.
    rewrite/aite.
    apply functional_extensionality => v.
    
    case Hv : (v \in s).
    - pose proof (H v Hv).
      exact H0.
    - reflexivity.
Qed.


(* ! # Constant assignments *)

Definition all_tt {V : finType} : assignment V :=
  fun _ => true.

Definition all_ff {V : finType} : assignment V :=
  fun _ => false.


Theorem all_tt_eval_tt :
  forall (v : V), all_tt v = true.
Proof.
  intros v.
  reflexivity.
Qed.

Theorem all_ff_eval_ff :
  forall (v : V), all_ff v = false.
Proof.
  intros v.
  reflexivity.
Qed.
  


End agree_on.
