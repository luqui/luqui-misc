Require Import Future.
Require Import Arith.

Set Implicit Arguments.

(* A discrete model of futures using nats as times, and (nat,a) as futures,
 * to show the consistency of the axioms *)

Module Future_NatModel : FutureTheory.
  Definition Time := nat.
  Definition TimeLT := le.
  Notation "A :< B" := (TimeLT A B) (at level 30, no associativity).

  Definition transitive := le_trans.
  Definition antisym := le_antisym.
  Definition reflexive := le_n.

  (* Verbatim from Future.v.  A weakness of coq that I have to repeat them. *)
  Definition LowerBound a b inf := (inf :< a * inf :< b)%type.
  Definition GreatestLowerBound a b inf :=
     (LowerBound a b inf * (forall i', LowerBound a b i' -> i' :< inf))%type.
  
  Definition glb := Min.min.

  Lemma min_glb : forall a b c, (c <= a) -> (c <= b) -> (c <= Min.min a b).
   intros.
   destruct (Min.min_dec a b) ; rewrite e ; assumption.
  Qed.
  
  Theorem isglb : forall a b, GreatestLowerBound a b (glb a b).
   intros.
   unfold GreatestLowerBound, LowerBound.
   split.
    split.
     exact (Min.le_min_l a b).
     exact (Min.le_min_r a b).
    intros.
    destruct H.
    refine (min_glb t t0).
  Qed.
   
  Definition Future (t:Time) (a:Type) := a.

  Definition pure a t (x:a) := x : Future t a.
  Definition ap t a b (f : Future t (a -> b)) (x : Future t a) := f x : Future t b.
  Definition deduce t t' a (H : t :< t') := (fun x => x) : Future t' (Future t a -> a).

  (* Verbatim from Future.v again. Ugh. *)
  Definition mapF A B t (f:A->B) fut := ap (pure t f) fut.

  Property prop_identity : forall t t' a (f:Future t' a), forall (h : t :< t'), 
         ap (deduce h) (mapF t (pure t) f) = f.
   auto.
  Qed.

  Property prop_pure_commute : forall a t (x:Future t a), pure t x = mapF t (pure t) x.
   auto.
  Qed.

  Property prop_assoc : forall a ta tb tc (x:Future tc (Future tb (Future ta a))), forall (Hab : ta :< tb) (Hbc : tb :< tc),
    ap (deduce (transitive Hab Hbc)) (ap (deduce Hbc) x) 
    = ap (deduce Hbc) (mapF tc (ap (deduce Hab)) x).
   auto.
  Qed.
  
  Property quasitotality : forall t t', Future (glb t t') (t :< t' + t' :< t).
   intros.
   unfold Future.
   destruct (le_ge_dec t t').
   left ; assumption.
   right ; assumption.
  Qed.
End Future_NatModel.